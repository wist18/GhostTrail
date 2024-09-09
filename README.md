# GhostTrail

GhostTrail is a tool designed to identify Speculative Concurrent Use-After-Free (SCUAF) vulnerabilities in C and C++ programs running on 64-bit Linux systems. This repository contains the implementation of GhostTrail, which utilizes LLVM for both intra-procedural and inter-procedural analysis on the intermediate representation (IR) of the Linux kernel.

## Prerequisites

- Git
- LLVM and Clang (built from source)
- CMake and Ninja
- Linux kernel source code

## Installation

1. **Clone the Repository:**
   ```sh
   git clone https://github.com/wist18/GhostTrail
   cd GhostTrail
   ```

2. **Clone the LLVM project:**
   ```sh
   task get-llvm
   ```

3. **Configure the LLVM project:**
   ```sh
   task config-llvm
   ```

4. **Build the LLVM project:**
   ```sh
   task build-llvm
   ``` 

5. **Clone the Linux kernel:**
   ```sh
   task get-linux
   ``` 

6. **Configure the LLVM project:**
   ```sh
   task config-linux
   ```

7. **Build the LLVM project:**
   ```sh
   task build-linux
   ``` 

## Usage

### Generate Bytecode (.bc) Files

To extract `.bc` files from the Linux kernel, run:

```sh
task gen-linux-bc
```

### Generate LLVM IR (.ll) Files

To generate `.ll` files from the bytecode, run:

```sh
task gen-linux-ll
```

## Build and Run LLVM Passes (Work in Progress, but if you followed until now, you should have the target code into bitcode and LLVM-IR formats)

> **⚠️ Important Warning:**
>
> Note that by default, the build and run pass is `syncprimitives.so`. If you want to change this, please modify the corresponding task in the `Taskfile.yml` and update it with the name of your pass. Also, ensure the naming of the `.cpp` file where your pass is implemented matches your new configuration.


### Build the LLVM Pass:

```sh
task build-pass
```

### Run the LLVM Pass:

```sh
python3 run_pass.py
```

