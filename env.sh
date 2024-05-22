#!/bin/bash

# Set environment variables
export LLVMPREFIX="$PWD/llvm-project/build"
export CLANG="$LLVMPREFIX/bin/clang"
export CC="$LLVMPREFIX/bin/clang"
export CXX="$LLVMPREFIX/bin/clang++"
export OPT="$LLVMPREFIX/bin/opt"
export LD="$LLVMPREFIX/bin/ld.lld"
export LLVM_AR="$LLVMPREFIX/bin/llvm-ar"
export LLVM_NM="$LLVMPREFIX/bin/llvm-nm"
export LLVM_OBJCOPY="$LLVMPREFIX/bin/llvm-objcopy"
export LLVM_OBJDUMP="$LLVMPREFIX/bin/llvm-objdump"
export LLVM_STRIP="$LLVMPREFIX/bin/llvm-strip"
export LLVM_LINK="$LLVMPREFIX/bin/llvm-link"
export LLVM_CONFIG="$LLVMPREFIX/bin/llvm-config"
export LLVM_DIS="$LLVMPREFIX/bin/llvm-dis"
export LLVM_COMPILER="$LLVMPREFIX/bin/clang"
export HOSTCC=clang
export HOSTCXX=clang++
export BRUH='bruh'
# Debugging echo statements
echo "LLVMPREFIX is set to: $LLVMPREFIX"
echo "CLANG is set to: $CLANG"
echo "CC is set to: $CC"
echo "CXX is set to: $CXX"
echo "OPT is set to: $OPT"
echo "LD is set to: $LD"
echo "LLVM_AR is set to: $LLVM_AR"
echo "LLVM_NM is set to: $LLVM_NM"
echo "LLVM_OBJCOPY is set to: $LLVM_OBJCOPY"
echo "LLVM_OBJDUMP is set to: $LLVM_OBJDUMP"
echo "LLVM_STRIP is set to: $LLVM_STRIP"
echo "LLVM_LINK is set to: $LLVM_LINK"
echo "LLVM_CONFIG is set to: $LLVM_CONFIG"
echo "LLVM_DIS is set to: $LLVM_DIS"
echo "LLVM_COMPILER is set to: $LLVM_COMPILER"
echo "HOSTCC is set to: $HOSTCC"
echo "HOSTCXX is set to: $HOSTCXX"
echo "BRUH is set to: $BRUH"
