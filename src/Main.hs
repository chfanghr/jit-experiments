{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Exception (throwIO)
import Control.Monad.Except (Except, MonadError (throwError), runExcept)
import Data.Binary.Put (putWord32le, runPut)
import Data.Bits (Bits (shiftL, (.&.)), (.|.))
import Data.ByteString qualified as BS
import Foreign.C.Types (CSize)
import Foreign.Marshal.Array (pokeArray)
import Foreign.Ptr (FunPtr, Ptr, castFunPtrToPtr, castPtr, nullPtr, ptrToIntPtr)
import MMAP (mapAnonymous, mapPrivate, mkMmapFlags, mmap, protExec, protRead, protWrite)
import Optics ((^.))
import Optics.State.Operators ((%=))
import Optics.TH (makeFieldLabelsNoPrefix)
import System.Exit (ExitCode (ExitFailure))
import System.Posix (RTLDFlags (RTLD_GLOBAL, RTLD_LAZY), dlopen, dlsym)
import Unsafe.Coerce (unsafeCoerce)

data Val
  = I Int64 -- Integer
  | R Reg -- Register
  | A Word32 -- Address
  deriving stock (Eq, Show)

-- Given an integral value, (unsafely, in a sense that the vaule will be
-- silently truncated to 32 bits) convert it into a little endian array of
-- bytes.
bytes :: (Integral a) => a -> [Word8]
bytes = BS.unpack . BS.toStrict . runPut . putWord32le . fromIntegral

-- 64 bit registers
data Reg
  = RAX -- Accumulator
  | RCX -- Counter (Loop counter)
  | RDX -- Data
  | RBX -- Base / General purpose
  | RSP -- Cuurent stack pointer
  | RBP -- Previous stack frame link
  | RSI -- Source index pointer
  | RDI -- Destination index pointer
  deriving stock (Eq, Show)

-- Index of each register.
-- TODO: Should probably use Bounded/Enum.
index :: Reg -> Word8
index RAX = 0
index RCX = 1
index RDX = 2
index RBX = 3
index RSP = 4
index RBP = 5
index RSI = 6
index RDI = 7

-- Subset of x86 instructions.
data Instr
  = Ret
  | Mov Val Val
  | Add Val Val
  | Sub Val Val
  | Mul Val
  | IMul Val Val
  | Xor Val Val
  | Inc Val
  | Dec Val
  | Push Val
  | Pop Val
  | Call Val
  | Loop Val
  | Nop
  | Syscall
  deriving stock (Show)

data JITMemory = JITMemory
  { instrs :: [Instr] -- Accumulated instructions
  , mach :: [Word8] -- Accumulated machine code
  , iCount :: Word32
  , memPtr :: Word32
  , memOff :: Word32
  }
  deriving stock (Show)

makeFieldLabelsNoPrefix ''JITMemory

type X86 a = StateT JITMemory (Except String) a

assemble :: X86 a -> Either String JITMemory
assemble = runExcept . executingStateT initialState
  where
    initialState :: JITMemory
    initialState = JITMemory [] [] 0 0 0

-- Add machine code to the JIT memory
emit :: [Word8] -> X86 ()
emit mach = do
  #mach %= (++ mach) -- Append the machine code
  #memOff %= (+ fromIntegral (length mach)) -- Adjust the memory offset by the length of instructions added

-- Convert an integer to an intermediate value and emit it. Unsafe.
imm32 :: (Integral a) => a -> X86 ()
imm32 = emit . bytes

-- Registers
rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi :: Val
rax = R RAX
rcx = R RCX
rdx = R RDX
rbx = R RBX
rsp = R RSP
rbp = R RBP
rsi = R RSI
rdi = R RDI

ret :: X86 ()
ret = emit [0xc3]

add :: Val -> Val -> X86 ()
-- add rax, <imm32>
add (R RAX) (I r) = do
  emit [0x48] -- REX.W
  emit [0x05] -- ADD
  imm32 r
-- add <reg>, <reg>
add (R l) (R r) = do
  emit [0x48] -- REX.W
  emit [0x01] -- ADD
  emit [0xC0 .|. index r `shiftL` 3 .|. index l]
add _ _ = badInstr

sub :: Val -> Val -> X86 ()
sub (R RAX) (I r) = do
  emit [0x48] -- REX.W
  emit [0x2D] -- SUB
  imm32 r
sub (R l) (R r) = do
  emit [0x48] -- REX.W
  emit [0x29] -- SUB
  emit [0xc0 .|. index r `shiftL` 3 .|. index l]
sub _ _ = badInstr

imul :: Val -> Val -> X86 ()
imul (R l) (I r) = do
  emit [0x48] -- REX.W
  emit [0x69] -- IMUL
  emit [0xC0 .|. index l]
  imm32 r
imul (R l) (R r) = do
  emit [0x48] -- REX.W
  emit [0x0F]
  emit [0xAF] -- IMUL
  emit [0xC0 .|. index r `shiftL` 3 .|. index l]
imul _ _ = badInstr

mov :: Val -> Val -> X86 ()
-- mov <reg>, <reg>
mov (R dst) (R src) = do
  emit [0x48] -- REX.W
  emit [0x89] -- MOV
  emit [0xC0 .|. index src `shiftL` 3 .|. index dst]
-- mov <reg>, <imm32>
mov (R dst) (I src) = do
  emit [0x48] -- REX.W
  emit [0xC7] -- MOV
  emit [0xC0 .|. (index dst .&. 7)]
  imm32 src
mov _ _ = badInstr

inc :: Val -> X86 ()
inc (R dst) = do
  emit [0x48] -- REX.W
  emit [0xFF] -- INC
  emit [0xC0 + index dst]
inc _ = badInstr

dec :: Val -> X86 ()
dec (R dst) = do
  emit [0x48] -- REX.W
  emit [0xFF] -- DEC
  emit [0xC0 + (index dst + 8)]
dec _ = badInstr

badInstr :: X86 ()
badInstr = lift $ throwError "bad instruction"

-- Given the size, allocate a chunk of readable/writable/executable memory off the
-- haskell managed heap using mmap(2).
allocate :: CSize -> IO (Ptr Word8)
allocate size = castPtr <$> mmap nullPtr size prot flags (-1) 0
  where
    prot = protRead <> protWrite <> protExec
    flags = mkMmapFlags mapPrivate mapAnonymous

-- Cast a pointer to Word32. This is useful for passing the address on the haskell
-- heap to the JITed code.
-- TODO: the name of this function can be a bit confusing.
heapPtr :: Ptr a -> Word32
heapPtr = fromIntegral . ptrToIntPtr

-- Grab the function pointer of the given symbol in the memory space of the process.
extern :: String -> IO Word32
extern sym = do
  -- From the man page of mmap(2): "If filename is NULL, then the returned handle is for the main
  -- program.". Haskell runtime links against libc by default and we want to make symbols in the
  -- libc available to the JITed code.
  dl <- dlopen "" [RTLD_LAZY, RTLD_GLOBAL]
  fnPtr <- dlsym dl sym
  pure $ heapPtr $ castFunPtrToPtr fnPtr

-- Copy machine code to the memory, and return the callable function.
jit :: Ptr Word8 -> [Word8] -> IO (IO Int)
jit mem machCode = do
  pokeArray mem machCode
  pure $ unsafeGetFunction mem

-- From https://wiki.haskell.org/Foreign_Function_Interface:
-- To call a function pointer from Haskell, GHC needs to convert between its own calling convention
-- and the one expected by the foreign code. To create a function doing this conversion, you must
-- use "dynamic" wrappers:
foreign import ccall "dynamic"
  mkFn :: FunPtr (IO Int) -> IO Int

-- Use the FFI to synthesize the function pointer to the memory and invoke it.
unsafeGetFunction :: Ptr Word8 -> IO Int
unsafeGetFunction ptr =
  let fnPtr = unsafeCoerce @_ @(FunPtr (IO Int)) ptr in mkFn fnPtr

main :: IO ()
main = do
  let jitSize = 256 * 1024
  ptr <- allocate jitSize
  mach <- case assemble arithDemo of
    Left err -> do
      putStrLn $ "fail to assemble: " <> err
      throwIO $ ExitFailure 1
    Right s -> pure $ s ^. #mach
  fn <- jit ptr mach
  res <- fn
  print res
  where
    arithDemo :: X86 ()
    arithDemo = do
      mov rax (I 69)
      add rax (I 69)
      sub rax (I 69)
      imul rax (I 69)
      ret
