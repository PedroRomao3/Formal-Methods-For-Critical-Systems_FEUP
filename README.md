# Project 1: Alloy Verification

This project for **M.EIC037: Formal Methods For Critical Systems (2024/2025)** focuses on modeling the high-level functionality of an email application using **Alloy**.

## Project Components

### 1. Mail Application Modeling (16 pts)
* **Objective**: Build a formal model of an email app focusing on mailboxes, messages, and operations.
* **System Structure**: The model includes 4 predefined system mailboxes (Inbox, Drafts, Trash, Sent) and zero or more user-created mailboxes.
* **Logic**: Define state-transformer predicates for operations like creating, moving, sending, and receiving messages, as well as deleting and purging mailboxes.
* **Verification**: 
    * **Test Scenarios**: Model 10 specific behaviors (e.g., messages moving to Sent, trash being emptied) as sanity checks.
    * **Assertions**: Formulate and check 16 expected temporal properties to ensure system correctness.
    * **Invalid Properties**: Use negation to find counterexample traces for properties expected to be satisfied by at least one execution.

### 2. Improved Mail App (2.5 pts)
* **Objective**: Refine behavior or add new functionalities approved by the lecturer.
* **Requirement**: Model the new behavior and follow all steps to ensure expected performance.

### 3. Report (1.5 pts)
* **Objective**: Submit a short report (max 4 pages) discussing improvements and validation steps.

## Required Files
* `proj1.als`: Initial model solution.
* `proj1-improved.als`: Enhanced version of the model.
* `Report.pdf`: Technical report.

---
**Note:** All code must be documented with comments for preconditions, post-conditions, and frame conditions. Groups consist of three people.

# Project 2: Dafny Verification

This project focuses on the formal implementation and verification of algorithms using **Dafny**.

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
