# Frama-C Research Repository

## Overview

This repository contains research materials and examples for **Frama-C**, a comprehensive platform for analyzing C programs. Frama-C (Framework for Modular Analysis of C code) is an open-source extensible framework designed to support various static analysis techniques for C programs. It provides a collection of pluggable analyzers that can be used individually or combined to verify different properties of C code.

This repository focuses on the four main analyzers of Frama-C:
- **EVA** (Evolved Value Analysis) - Abstract interpretation-based value analysis
- **WP** (Weakest Precondition) - Deductive verification using proof obligations
- **RTE** (Runtime Error) - Automatic generation of runtime error annotations
- **Slicing** - Program slicing for dependency analysis

Each analyzer has its own directory containing documentation, use cases, and practical C code examples.

## Installing Frama-C

### Linux Installation

#### Ubuntu/Debian

1. **Using APT package manager** (easiest method):
   ```bash
   sudo apt-get update
   sudo apt-get install frama-c
   ```

2. **Using OPAM** (for latest version):
   ```bash
   # Install OPAM if not already installed
   sudo apt-get install opam
   
   # Initialize OPAM
   opam init
   eval $(opam env)
   
   # Install Frama-C
   opam install frama-c
   ```

3. **Building from source**:
   ```bash
   # Install dependencies
   sudo apt-get install build-essential autoconf ocaml ocaml-findlib
   
   # Download and extract Frama-C from https://frama-c.com/download.html
   wget https://frama-c.com/download/frama-c-XX.X.tar.gz
   tar -xzf frama-c-XX.X.tar.gz
   cd frama-c-XX.X
   
   # Configure, build, and install
   autoconf
   ./configure
   make
   sudo make install
   ```

#### Fedora/RHEL/CentOS

```bash
# Using DNF
sudo dnf install frama-c

# Or using OPAM (see Ubuntu instructions above)
```

### Windows Installation

#### Method 1: Using WSL (Windows Subsystem for Linux) - Recommended

1. **Install WSL**:
   - Open PowerShell as Administrator and run:
     ```powershell
     wsl --install
     ```
   - Restart your computer if prompted

2. **Install Frama-C in WSL**:
   - Open WSL terminal and follow the Linux installation instructions above

#### Method 2: Using Cygwin

1. **Install Cygwin** from https://www.cygwin.com/

2. **During installation, select the following packages**:
   - gcc-core
   - make
   - ocaml
   - autoconf

3. **Install OPAM in Cygwin**:
   ```bash
   # Download and install OPAM
   wget https://github.com/ocaml/opam/releases/download/2.1.0/opam-2.1.0-x86_64-linux
   mv opam-2.1.0-x86_64-linux /usr/local/bin/opam
   chmod +x /usr/local/bin/opam
   
   # Initialize and install Frama-C
   opam init
   eval $(opam env)
   opam install frama-c
   ```

#### Method 3: Using Pre-built Binaries

1. Download the Windows binary from the official Frama-C website: https://frama-c.com/download.html
2. Extract the archive to a directory (e.g., `C:\Program Files\Frama-C`)
3. Add the Frama-C binary directory to your system PATH

### Verifying Installation

After installation, verify that Frama-C is properly installed:

```bash
frama-c -version
```

You should see output showing the Frama-C version and available plugins.

## Repository Structure

```
Frama-C_research/
├── README.md                 # This file
├── EVA/                      # Evolved Value Analysis
│   ├── README.md            # EVA documentation
│   └── example.c            # EVA example code
├── WP/                       # Weakest Precondition
│   ├── README.md            # WP documentation
│   └── example.c            # WP example code
├── RTE/                      # Runtime Error
│   ├── README.md            # RTE documentation
│   └── example.c            # RTE example code
└── Slicing/                  # Program Slicing
    ├── README.md            # Slicing documentation
    └── example.c            # Slicing example code
```

## Getting Started

1. Install Frama-C following the instructions above
2. Navigate to any analyzer directory (EVA, WP, RTE, or Slicing)
3. Read the analyzer-specific README.md for details
4. Run the example code with the suggested commands

## Additional Resources

- Official Frama-C website: https://frama-c.com/
- Frama-C documentation: https://frama-c.com/html/documentation.html
- Frama-C user manual: https://frama-c.com/download/frama-c-user-manual.pdf
- ACSL (ANSI/ISO C Specification Language): https://frama-c.com/acsl.html

## License

This repository is for educational and research purposes.