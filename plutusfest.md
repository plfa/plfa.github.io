# An Introduction to Plutus

Using smart contracts can be a smart idea. Or extremely stupid.

The value of a blockchain is enhanced if it can execute smart
contracts. Smart contracts allow an individual or a group to authorise
code that automatically enable transfer of resources on the chain,
without requiring further approval. A classic example is
crowd-funding. Say Jane wants to raise funds to make a film, say
$500,000 by 1 April. She uses a site such as Kickstarter to seek
funding. If donations reach the set total before the set date, the
website forwards the accumulated funds to Jane, otherwise it returns
the funds to their original donors. This requires that everyone trusts
those running the website to do the right thing, and not (for
instance) to run off with the funds themselves. A smart contract
enables the same behaviour without the need for trust. Jane registers
on Cardano (or some other blockchain) a smart contract
that encodes the behaviour described above, and anyone can read it
to confirm that it behaves as advertised before sending to it their
Adas (or other cryptocurrency).

The term "smart contract" was coined by Nick Szabo toward the end of
the last millennium, but the first widespread implementation was by
Vitalik Buterin and colleagues. It was named Ethereum, and went live
in July 2015. Ethereum is currently capitalised at around $11B USD. It
has been subject to a sequence of attacks and mishaps, such as the DAO
exploit (17 June 2016, 3.6M ETH, then worth USD $80M), the Parity
attack (19 July 2017, 150K ETH, then worth USD $30M, with another 377K
ETH saved by "White Hat" hackers), and and the Parity accident (514K
ETH frozen and unrecoverable, then worth USD $153M) [1][1]. That's
only a few from a much larger list. One recent academic paper
described a technique that can automatically check all smart contracts
on Ethereum for a class of potential exploits, and reports that 10% of
all funds on the platform are at risk [2][2]. IOHK runs Ethereum
Classic, which guarantees to preserve the original Ethereum system,
and hence also guarantees to preserve all its vulnerabilities.

[1]: https://medium.com/solidified/the-biggest-smart-contract-hacks-in-history-or-how-to-endanger-up-to-us-2-2-billion-d5a72961d15d
[2]: 
http://www.nevillegrech.com/madmax-oopsla18.pdf

Many Ethereum exploits are due to poor design choices in the
software that executes smart contracts, both the low-level
Ethereum Virtual Machine (EVM), and the high-level language
that compiles into it, Solidity.  For instance, 
many accidents and scams arise from the fact that the
EVM does not raise an exception on integer overflow, and
others arise from poor handling of unexpected messages in
the object-oriented design of Solidity.  Other times the
issues are more subtle, as with the DAO bug.  The first time
I saw it, I thought, "I never would have thought of that",
although some researchers more familiar with distributed systems
regard it as a rookie error.  One of the trickiest problems with
smart contracts is that if you do later uncover a fault, it can
only be changed if you've designed your smart contract to be
updated. And doing that introduces its own vulnerabilities.

# Plutus Coordination, Plutus Tx, and Plutus Core

Plutus is the smart contract language of Cardano. It is, in fact,
a collection of languages.

Our crowdfunder example above is one of the standards for learning
Ethereum and Solidity, the equivalent of "Hello, World!".  





Outline of blog post
--------------------

* What I like about IOHK: peer-review and Haskell

* Smart Contract vulnerabilities in Ethereum

* Plutus Coordination, Plutus Tx, and Plutus Core

* Why Plutus Core is System F omega

* Recursion (recursive values & mutually recursive types)

* UTxO vs Accounts

* Sized integers




Outline of intro talk (5 min)
-----------------------------

* What I like about IOHK: peer-review and Haskell

* Manuel's clever idea: integrate off-chain and on-chain

* Plutus Core is System F omega


Outline of keynote (30 min)
---------------------------

* Why System F omega?

  + Advertise Propositions as Types 

  + Scott encoding vs Church encoding

  + Only a factor of three in cost

* Unbounded integers vs sized integers

* Reiterate material on Plutus Platform?

* Intro to Recursion in Plutus Core

* Intro to Agda model - praise James

  + Advertise PLFA (use pictures on blog)

* Mention Marlowe

* Mention IELE and RV

* Mention QuickCheck

* Mention Duncan & Philipp's work

[What photos and artifacts should I use?]
