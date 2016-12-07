### pitypes
This repository contains haskell implementations of various Pi Calculus type systems as described in corresponding research papers.

At present, these implementations are of type systems only. Implementations of operational semantics in the form of interpreters may follow.

#### LinearPi.hs

This file is an implementation of the type system described by Kobayashi, Pierce & Turner's July 1995 paper, '[Linearity and the Pi-Calculus](http://dl.acm.org/citation.cfm?id=330251)'. The paper describes a type system with 'use-once' channel types inspired by linear logic.


#### Session.hs

This file is an implementation of the type system described by Honda, Vasconcelos & Kubo's April 1998 paper, '[Language Primitives and Type Discipline for Structured Communication-Based Programming](http://dl.acm.org/citation.cfm?id=651876)'. The paper describes a type system based on *sessions*, which are 2-way communication protocols. The type system ensures that processes behave according to a specific session, and that the communication partner has the exact complimentary session, preventing communication errors.
