## pitypes
This repository contains haskell implementations of various Pi Calculus type systems as described in corresponding research papers.

At present, these implementations are of type systems only. Implementations of operational semantics in the form of interpreters may follow.

#### LinearPi.hs

This file is an implementation of the type system described by Kobayashi, Pierce & Turner's July 1995 paper, '[Linearity and the Pi-Calculus](http://dl.acm.org/citation.cfm?id=330251)'. The paper describes a type system with 'use-once' channel types inspired by linear logic.

##### Notes on Linearity and the Pi-Calculus

Functional computation in the Pi Calculus typically employs return channels for results. Functions typically return only once, and thus return channels are used only once. The ability to declare a channel as a use-once channel and enforce this propery at compile-time can therefore prevent errors resulting from misuse of return channels.

Channel types contain three pieces of information:
    - Multiplicity - either 1 or +. 1-channels must be used exactly once, +-channels can be used multiple times.
    - Capability (polarity) - a set of elements over the alphabet { I, O } where I represents input and O represents output. a channel with { I, O } can do input and output, a channel with { I } can do only input, a channel with { O } can do only output, and a channel with { } cannot do any further communication.
    - Message type - the type of data sent over the channel

The rule E-Par splits the typing environment to type the left and right hand side of parallel composition. We can think of the left and right splits of the environment as copies of the original environment, where the capability sets for each type are split accordingly. For example, if x is a 1-channel on which p sends and q receives in p | q, we split the environment such that in the environment with which we check p, x has capability output, and in the environment with which we check q, x has capability input. Computing the left and right environment is tricky. The paper suggests 'crossing off' capabilities on the left, and then passing the resulting environment to the right and crossing off, ensuring every limited channel gets crossed off. My approach was to try all possible splits and just go with any that works.


#### Session.hs

This file is an implementation of the type system described by Honda, Vasconcelos & Kubo's April 1998 paper, '[Language Primitives and Type Discipline for Structured Communication-Based Programming](http://dl.acm.org/citation.cfm?id=651876)'. The paper describes a type system based on *sessions*, which are 2-way communication protocols. The type system ensures that processes behave according to a specific session, and that the communication partner has the exact complimentary session, preventing communication errors.
