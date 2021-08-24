# Index of exercises

## chapter01-basics

- [`chapter01-basics/exercises/exercise01.dfy`](chapter01-basics/exercises/exercise01.dfy)<br>**Lemmas and assertions**

- [`chapter01-basics/exercises/exercise02.dfy`](chapter01-basics/exercises/exercise02.dfy)<br>**Boolean logic**

- [`chapter01-basics/exercises/exercise03.dfy`](chapter01-basics/exercises/exercise03.dfy)<br>**Functions**

- [`chapter01-basics/exercises/exercise04.dfy`](chapter01-basics/exercises/exercise04.dfy)<br>**Predicates**

- [`chapter01-basics/exercises/exercise05.dfy`](chapter01-basics/exercises/exercise05.dfy)<br>**Sets**

- [`chapter01-basics/exercises/exercise06.dfy`](chapter01-basics/exercises/exercise06.dfy)<br>**More set tools**

- [`chapter01-basics/exercises/exercise07.dfy`](chapter01-basics/exercises/exercise07.dfy)<br>**Sequences**

- [`chapter01-basics/exercises/exercise08.dfy`](chapter01-basics/exercises/exercise08.dfy)<br>**Type synonyms**

- [`chapter01-basics/exercises/exercise09.dfy`](chapter01-basics/exercises/exercise09.dfy)<br>**Struct (product) datatypes.**

- [`chapter01-basics/exercises/exercise10.dfy`](chapter01-basics/exercises/exercise10.dfy)<br>**include directive and Union (sum) datatypes**

- [`chapter01-basics/exercises/exercise11.dfy`](chapter01-basics/exercises/exercise11.dfy)<br>**Algebraic datatypes in their full glory.**

- [`chapter01-basics/exercises/exercise12.dfy`](chapter01-basics/exercises/exercise12.dfy)<br>**More with algebraic datatypes.**

- [`chapter01-basics/exercises/exercise13.dfy`](chapter01-basics/exercises/exercise13.dfy)<br>**Quantifiers**

- [`chapter01-basics/exercises/exercise14.dfy`](chapter01-basics/exercises/exercise14.dfy)<br>**Maps. Set, Map and Sequence comprehensions.**

- [`chapter01-basics/exercises/exercise15.dfy`](chapter01-basics/exercises/exercise15.dfy)<br>**Comprehensions, the finite heuristic, axioms, recursion**

- [`chapter01-basics/exercises/exercise16.dfy`](chapter01-basics/exercises/exercise16.dfy)<br>**IsEven** -- Hoare logic

- [`chapter01-basics/exercises/exercise18.dfy`](chapter01-basics/exercises/exercise18.dfy)<br>**Fibo** -- Recursion challenge.

- [`chapter01-basics/exercises/exercise19.dfy`](chapter01-basics/exercises/exercise19.dfy)<br>**FindMax** -- Loop invariants.

- [`chapter01-basics/exercises/exercise20.dfy`](chapter01-basics/exercises/exercise20.dfy)<br>**IsSeqSorted** -- Build an entire imperative loop method implementation with loop invariants.

- [`chapter01-basics/exercises/exercise21.dfy`](chapter01-basics/exercises/exercise21.dfy)<br>**Binary Search** -- Method implementation; writing a Hoare spec.

- [`chapter01-basics/exercises/exercise22.dfy`](chapter01-basics/exercises/exercise22.dfy)<br>**Binary Tree Is Sorted** -- Prove an implementation meets its spec. Practice with proof diagnosis.

- [`chapter01-basics/exercises/exercise23.dfy`](chapter01-basics/exercises/exercise23.dfy)<br>**Binary Tree Search** -- Implement search in a binary tree and prove it works. Practice with proof diagnosis.

- [`chapter01-basics/exercises/lib_directions.dfy`](chapter01-basics/exercises/lib_directions.dfy) -- Library for exercises 10 & 13

- [`chapter01-basics/exercises/lib_lunch.dfy`](chapter01-basics/exercises/lib_lunch.dfy) -- Library for exercises 12 & 13

## chapter02-spec

- [`chapter02-spec/exercises/exercise01.dfy`](chapter02-spec/exercises/exercise01.dfy)<br>**IsPrime I** -- Basic specification.

- [`chapter02-spec/exercises/exercise02.dfy`](chapter02-spec/exercises/exercise02.dfy)<br>**IsPrime II** -- Working with an implementation proof

- [`chapter02-spec/exercises/exercise03.dfy`](chapter02-spec/exercises/exercise03.dfy)<br>**Merge Sort** -- More specification practice.

## chapter03-sm

- [`chapter03-sm/exercises/exercise01.dfy`](chapter03-sm/exercises/exercise01.dfy)<br>**Coke Machine** -- The first state machine specification exercise: fill in actions.

- [`chapter03-sm/exercises/exercise02.dfy`](chapter03-sm/exercises/exercise02.dfy)<br>**Dining Philosophers** -- A more challenging state machine: define the state datatype.

- [`chapter03-sm/exercises/exercise03.dfy`](chapter03-sm/exercises/exercise03.dfy)<br>**Single-Server Lock Service Model** -- A complex state machine including a Safety predicate on the state type.

## chapter04-inv

- [`chapter04-inv/exercises/exercise01.dfy`](chapter04-inv/exercises/exercise01.dfy)<br>**Crawler** -- Introduction to inductive invariants -- implement the visualization from the lecture.

- [`chapter04-inv/exercises/exercise02.dfy`](chapter04-inv/exercises/exercise02.dfy)<br>**Single-Server Lock Service Proof** -- A more realistic invariant proof of the previous chapter's lock service.

## chapter05-dsm

- [`chapter05-dsm/exercises/exercise01.dfy`](chapter05-dsm/exercises/exercise01.dfy)<br>**Two Phase Commit Model** -- Model a distributed protocol using compound state machines.

- [`chapter05-dsm/exercises/exercise02.dfy`](chapter05-dsm/exercises/exercise02.dfy)<br>**Two Phase Commit Safety Specification Predicate** -- Express the English Atomic Commit safety properties as predicates over the compound state machine model from exercise01.

- [`chapter05-dsm/exercises/exercise03.dfy`](chapter05-dsm/exercises/exercise03.dfy)<br>**Two Phase Commit Safety Proof** -- Prove that the 2PC distributed system (exercise01) accomplishes the Safety spec (exercise02)

- [`chapter05-dsm/exercises/model_for_ex03.dfy`](chapter05-dsm/exercises/model_for_ex03.dfy) -- Given model for exercise03

## chapter06-refine

- [`chapter06-refine/exercises/exercise01.dfy`](chapter06-refine/exercises/exercise01.dfy)<br>**Sharded KV Store with Synchronous Communication** -- Build a refinement from a protocol (distributed sharded state) to a specification (a logically-centralized abstract map).

- [`chapter06-refine/exercises/exercise02.dfy`](chapter06-refine/exercises/exercise02.dfy)<br>**State Machine Spec for Atomic Commit** -- Build an abstract behavioral model that captures the semantics of an evolving system to use as a refinement reference for its more-complicated implementation.

- [`chapter06-refine/exercises/exercise03.dfy`](chapter06-refine/exercises/exercise03.dfy)<br>**Property Lemmas for Atomic Commit** -- The state machine model captures AC2 nicely, but let's make it very clear that the model also obeys AC1, AC3 and AC4.

- [`chapter06-refine/exercises/exercise04.dfy`](chapter06-refine/exercises/exercise04.dfy)<br>**Refinement proof for 2PC** -- Show that Two Phase Commit refines the Atomic Commit sate machine spec.

- [`chapter06-refine/exercises/impl_model_for_ex04.dfy`](chapter06-refine/exercises/impl_model_for_ex04.dfy) -- Implementation state machine for refinement proof in exercise04.

- [`chapter06-refine/exercises/spec_model_for_ex04.dfy`](chapter06-refine/exercises/spec_model_for_ex04.dfy) -- Specification state machine for refinement proof in exercise04.

## chapter07

## chapter07-async-clients

- [`chapter07-async-clients/exercises/exercise01.dfy`](chapter07-async-clients/exercises/exercise01.dfy)<br>**KV Store Spec with Asynchronous Client Interface** -- Build a refinement from a protocol (distributed sharded state) to a specification (a logically-centralized abstract map).

## final-project

- [`final-project/exercises/exercise01.dfy`](final-project/exercises/exercise01.dfy)<br>**Final Project** -- Design a Sharded Hash Table (SHT) protocol and prove it is correct.

## midterm-project

- [`midterm-project/exercises/distributed_system.s.dfy`](midterm-project/exercises/distributed_system.s.dfy)<br>**DistributedSystem** -- DO NOT EDIT THIS FILE! It's a trusted file that specifies how hosts interact with one another over the network.

- [`midterm-project/exercises/exercise01.dfy`](midterm-project/exercises/exercise01.dfy)<br>**Midterm Project** -- Build a distributed lock server. Define how a host implements your protocol in host.i; write your safety spec and proof here.

- [`midterm-project/exercises/host.i.dfy`](midterm-project/exercises/host.i.dfy)<br>**Host protocol** -- Define the host state machine here: message type, state machine for executing one host's part of the protocol.

- [`midterm-project/exercises/network.s.dfy`](midterm-project/exercises/network.s.dfy)<br>**Network** -- DO NOT EDIT THIS FILE! It's a trusted file that specifies how the network delivers packets, allowing reorder and duplicate delivery.

