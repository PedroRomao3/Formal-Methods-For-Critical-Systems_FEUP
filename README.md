# Project 2: Dafny Verification

This project for **M.EIC037: Formal Methods For Critical Systems (2024/2025)** focuses on the formal implementation and verification of algorithms using **Dafny**.

## Project Components

### 1. Array Partitioning
* **Objective**: Implement an in-place version of the Dutch National Flag algorithm.
* **Logic**: Rearrange an array segment into three contiguous parts: elements $< X$, $= X$, and $> X$.
* **Verification**: Prove the implementation meets the partition specification using invariants and termination proofs.

### 2. Mail Application (12 pts)
* **Objective**: Formally specify a provided email client prototype (classes `MailApp` and `Mailbox`).
* **Tasks**: 
    * Define `isValid` predicates to link abstract ghost states with concrete states.
    * Add method contracts (pre/post-conditions) and class invariants.
    * Implement the `Message` class according to its formal specification.

### 3. Improved Mail Application (3 pts)
* **Objective**: Extend the application with new improved functionalities.
* **Requirement**: Fully verify the new behavior and document improvements at the top of the file.

## Required Files
* `Partition.dfy`: Array partition implementation.
* `Mail.dfy`: Initial verified mail solution.
* `Mail-improved.dfy`: Enhanced mail application.

---
**Note:** All code must be documented with comments for every line of specification to avoid penalties.
