# Virtual Memory Simulator

This repository contains my implementation of a **virtual memory management
simulator** written in C.  
The project focuses on **paging, address translation,
and memory abstraction**.

---

## Problem Overview

Modern operating systems rely on **virtual memory** to provide processes with
the illusion of a large, continuous address space while efficiently managing
limited physical memory.

This project simulates the core mechanisms of virtual memory, including:
- Virtual-to-physical address translation
- Page-based memory organization
- Memory access handling and abstraction

The goal is to model how an operating system manages memory rather than to
interact with real hardware.

---

## System Design

The simulator models a simplified virtual memory subsystem with the following
responsibilities:

- Managing virtual memory structures
- Translating virtual addresses into physical locations
- Handling memory accesses through well-defined abstractions
- Maintaining consistency between memory representations

All logic is implemented in a single, self-contained C module.

---

## Implementation Details (`vm.c`)

The `vm.c` file implements the core logic of the virtual memory simulator,
including:

- Virtual memory data structures
- Address translation logic
- Page-level memory handling
- Abstractions that separate virtual and physical memory concepts
- Error handling for invalid or out-of-bound memory accesses

The implementation follows the constraints and API specifications defined
in the assignment.

---

## My Contribution

As part of this assignment, I independently implemented:

- The complete virtual memory simulation logic in `vm.c`
- Page-based address translation mechanisms
- Memory access handling and validation
- Modular abstractions for virtual vs. physical memory
- A detailed written analysis explaining the design decisions

The implementation reflects a clear separation of concerns and models the
behavior of a virtual memory subsystem at a conceptual level. My specific contribution to the file starts at the "YOUR CODE STARTS HERE" line and ends at "YOUR CODE ENDS HERE".

---


