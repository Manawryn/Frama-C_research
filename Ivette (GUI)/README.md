# Ivette for Frama-C

**Ivette** is the modern, Electron-based Graphical User Interface (GUI) for the [Frama-C](https://frama-c.com/) source code analysis platform. Designed to replace the legacy GTK interface (`frama-c-gui`), Ivette provides a responsive, IDE-like experience for interacting with Frama-C analyzers like Eva (Evolved Value Analysis) and WP (Weakest Precondition).

---

## 🚀 Key Features (Pros)

* **Modern UX:** Built on Electron and React, offering a responsive, "VS Code-like" experience with dark/light themes, dockable panels, and smooth navigation.
* **Asynchronous Interaction:** Unlike the legacy GUI, Ivette runs as a separate client. It does not freeze while the Frama-C kernel is performing heavy calculations, allowing you to browse code while an analysis runs.
* **Client/Server Architecture:** Communicates with the Frama-C kernel via a robust server plugin, enabling better separation of concerns and stability.
* **Interactive AST:** Advanced Abstract Syntax Tree (AST) navigation, allowing you to click on variables and statements to see values, dependencies, and properties instantly.
* **State Management:** Better handling of session saving/loading and analysis parameters.

## ⚠️ Limitations (Cons)

* **Resource Usage:** As an Electron app, it consumes more RAM and disk space than the lightweight legacy GTK interface.
* **Setup Complexity:** Building from source (via Opam) requires a JavaScript ecosystem (Node.js, Yarn), which adds steps to the installation process.
* **Maturity:** While functionally capable, it is a newer tool. Some specific, niche features from the legacy `frama-c-gui` may still be in the process of being ported.
* **WSL Requirement (Windows):** Does not run as a native Windows `.exe`; it relies heavily on WSL (Windows Subsystem for Linux).

---

## 🛠 Prerequisites

Before running Ivette, ensure you have the core Frama-C platform installed.

* **OCaml Package Manager (Opam):** version 2.0+
* **Node.js:** Version 16+ (Required if bootstrapping from source)
* **Yarn:** (Required if bootstrapping from source)

---

## 📥 Installation

### 🐧 Linux

There are two ways to use Ivette on Linux: using the **AppImage** (easiest) or bootstrapping via **Opam**.

#### Method 1: AppImage (Recommended for Beginners)
1.  Download the latest `AppImage` from the [Frama-C Releases page](https://frama-c.com/fc-versions.html).
2.  Make the file executable and run it:
    ```bash
    chmod +x ivette-linux-x64.AppImage
    ./ivette-linux-x64.AppImage
    ```
    *Note: You still need `frama-c` installed on your system path for the analysis to work.*

#### Method 2: Via Opam (Source/Bootstrap)
If you installed Frama-C via Opam, Ivette is included as a wrapper script that bootstraps the installation.

1.  Install system dependencies (Debian/Ubuntu example):
    ```bash
    sudo apt install nodejs npm
    sudo npm install --global yarn
    ```
2.  Install Frama-C via Opam:
    ```bash
    opam install frama-c
    ```
3.  Run Ivette:
    ```bash
    ivette
    ```
    *First Run Note: The first time you run this command, it will automatically download the Electron binaries and compile the interface. This may take a few minutes.*

---

### 🪟 Windows

Frama-C and Ivette are **not** supported as native Windows applications. You must use **WSL2** (Windows Subsystem for Linux).

#### Step 1: Set up WSL2
1.  Open PowerShell as Administrator and run:
    ```powershell
    wsl --install
    ```
2.  Restart your computer and finish the Ubuntu setup.

#### Step 2: Install Dependencies in Ubuntu (WSL)
Open your Ubuntu terminal and install the necessary libraries (including GTK dependencies often required by the backend):
```bash
sudo apt update
sudo apt install opam make m4 gcc libgmp-dev libgtksourceview-3.0-dev libgnomecanvas2-dev