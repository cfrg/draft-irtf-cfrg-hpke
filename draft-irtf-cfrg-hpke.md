---
title: Hybrid Public Key Encryption
abbrev: HPKE
docname: draft-irtf-cfrg-hpke-latest
date:
category: info

ipr: trust200902
keyword: Internet-Draft

stand_alone: yes
pi: [toc, sortrefs, symrefs]

author:
 -  ins: R. L. Barnes
    name: Richard L. Barnes
    org: Cisco
    email: rlb@ipv.sx
 -  ins: K. Bhargavan
    name: Karthik Bhargavan
    org: Inria
    email: karthikeyan.bhargavan@inria.fr

informative:
  S01:
    title: A Proposal for an ISO Standard for Public Key Encryption (verison 2.1)
    target: http://www.shoup.net/papers/iso-2_1.pdf
    date: 2001
    authors:
      -
        ins: Victor Shoup
        org: IBM Zurich Research Lab, Saumerstr. 4, 8803 Ruschlikon, Switzerland
  ANSI:
    title: Public Key Cryptography for the Financial Services Industry -- Key Agreement and Key Transport Using Elliptic Curve Cryptography
    date: 2001
    authors:
      -
        ins:
        org: American National Standards Institute
  IEEE:
    title: IEEE 1363a, Standard Specifications for Public Key Cryptography - Amendment 1 -- Additional Techniques
    date: 2004
    authors:
      -
        ins:
        org: Institute of Electrical and Electronics Engineers
  ISO:
    title: ISO/IEC 18033-2, Information Technology - Security Techniques - Encryption Algorithms - Part 2 -- Asymmetric Ciphers
    date: 2006
    authors:
      -
        ins:
        org: International Organization for Standardization / International Electrotechnical Commission

  SECG:
    title: Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2
    target: https://secg.org/sec1-v2.pdf
    date: 2009

  MAEA10:
    title: A Comparison of the Standardized Versions of ECIES
    target: http://sceweb.sce.uhcl.edu/yang/teaching/csci5234WebSecurityFall2011/Chaum-blind-signatures.PDF
    date: 2010
    authors:
      -
        ins: V. Gayoso Martinez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: F. Hernandez Alvarez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: L. Hernandez Encinas
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: C. Sanchez Avila
        org: Polytechnic University, Madrid, Spain

  BNT19:
    title: "Nonces Are Noticed: AEAD Revisited"
    target: http://dx.doi.org/10.1007/978-3-030-26948-7_9
    date: 2019
    authors:
      -
        ins: M. Bellare
        org: University of California, San Diego
      -
        ins: R. Ng
        org: University of California, San Diego
      -
        ins: B. Tackmann
        org: IBM Research

  JKR96:
    title: Designated Verifier Proofs and Their Applications
    target: https://doi.org/10.1007%2F3-540-49677-7_30
    date: 1996
    authors:
      -
        ins: M. Jakobsson
        org: University of California, San Diego
      -
        ins: K. Sako
        org: NEC Corporation
      -
        ins: R. Impagliazzo
        org: University of California, San Diego

  TestVectors:
    title: HPKE Test Vectors
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/1e98830311b27f9af00787c16e2c5ac43abeadfb/test-vectors.json
    date: 2019

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar2
  NISTCurves: DOI.10.6028/NIST.FIPS.186-4
  GCM: DOI.10.6028/NIST.SP.800-38D

  fiveG:
    title: Security architecture and procedures for 5G System
    target: https://portal.3gpp.org/desktopmodules/Specifications/SpecificationDetails.aspx?specificationId=3169
    date: 2019

--- abstract

This document describes a scheme for hybrid public-key encryption
(HPKE).  This scheme provides authenticated public key encryption of
arbitrary-sized plaintexts for a recipient public key. HPKE works
for any combination of an asymmetric key encapsulation mechanism
(KEM), key derivation function (KDF), and authenticated encryption
with additional data (AEAD) encryption function. We provide
instantiations of the scheme using widely-used and efficient
primitives.

--- middle

# Introduction

"Hybrid" public-key encryption schemes (HPKE) that combine
asymmetric and symmetric algorithms are a substantially more
efficient solution than traditional public key encryption techniques
such as those based on RSA or ElGamal.  Encrypted messages convey an encryption
key encapsulated with a public-key scheme, along with one or more ciphertexts
encrypted using that key.  This type of public key encryption has many
applications in practice, for example:

* PGP {{?RFC6637}}
* Messaging Layer Security {{?I-D.ietf-mls-protocol}}
* Encrypted Server Name Indication {{?I-D.ietf-tls-esni}}
* Protection of 5G subscriber identities {{fiveG}}

Currently, there are numerous competing and non-interoperable standards and
variants for hybrid encryption, mostly based on ECIES, including ANSI X9.63
(ECIES) {{ANSI}}, IEEE 1363a {{IEEE}}, ISO/IEC 18033-2 {{ISO}}, and SECG SEC 1
{{SECG}}.  See {{MAEA10}} for a thorough comparison.  All of these existing
schemes have problems, e.g., because they rely on outdated primitives, lack
proofs of IND-CCA2 security, or fail to provide test vectors.

This document defines an HPKE scheme that provides a subset
of the functions provided by the collection of schemes above, but
specified with sufficient clarity that they can be interoperably
implemented and formally verified.

# Requirements Notation

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP14 {{!RFC2119}} {{!RFC8174}}  when, and only when, they appear in
all capitals, as shown here.

# Security Properties

As a hybrid authentication encryption algorithm, we desire security
against (adaptive) chosen ciphertext attacks (IND-CCA2 secure). The
HPKE variants described in this document achieve this property under
the Random Oracle model assuming the gap Computational Diffie
Hellman (CDH) problem is hard {{S01}}.

[[ TODO - Provide citations to these proofs once they exist ]]

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- Sender (S): Entity which sends an encrypted message.
- Recipient (R): Entity which receives an encrypted message.
- Ephemeral (E): A fresh random value meant for one-time use.
- `(skX, pkX)`: A KEM key pair used in role X; `skX` is the private
  key and `pkX` is the public key
- `pk(skX)`: The public key corresponding to private key `skX`
- `len(x)`: The length of the octet string `x`, expressed as a
  two-octet unsigned integer in network (big-endian) byte order
- `encode_big_endian(x, n)`: An octet string encoding the integer
  value `x` as an n-byte big-endian value
- `concat(x0, ..., xN)`: Concatenation of octet strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`
- `zero(n)`: An all-zero octet string of length `n`. `zero(4) =
  0x00000000`
- `xor(a,b)`: XOR of octet strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - GenerateKeyPair(): Generate a key pair (sk, pk)
  - Marshal(pk): Produce a fixed-length octet string encoding the
    public key `pk`
  - Unmarshal(enc): Parse a fixed-length octet string to recover a
    public key
  - Encap(pk): Generate an ephemeral, fixed-length symmetric key and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to pk
  - Decap(enc, sk): Use the private key `sk` to recover the ephemeral
    symmetric key from its encapsulated representation `enc`
  - AuthEncap(pkR, skS) (optional): Same as Encap(), but the outputs
    encode an assurance that the ephemeral shared key is known only
    to the holder of the private key `skS`
  - AuthDecap(skR, pkS) (optional): Same as Decap(), but the holder
    of the private key `skR` is assured that the ephemeral shared
    key is known only to the holder of the private key corresponding
    to `pkS`
  - Nenc: The length in octets of an encapsulated key from this KEM
  - Npk: The length in octets of a public key for this KEM

* A Key Derivation Function:
  - Hash(m): Compute the cryptographic hash of input message `m`
  - Extract(salt, IKM): Extract a pseudorandom key of fixed length
    from input keying material `IKM` and an optional octet string
    `salt`
  - Expand(PRK, info, L): Expand a pseudorandom key `PRK` using
    optional string `info` into `L` bytes of output keying material
  - Nh: The output size of the Hash and Extract functions in octets

* An AEAD encryption algorithm {{!RFC5116}}:
  - Seal(key, nonce, aad, pt): Encrypt and authenticate plaintext
    `pt` with associated data `aad` using secret key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`
  - Open(key, nonce, aad, ct): Decrypt ciphertext `ct` using
    associated data `aad` with secret key `key` and nonce `nonce`,
    returning plaintext message `pt` or the error value `OpenError`
  - Nk: The length in octets of a key for this algorithm
  - Nn: The length in octets of a nonce for this algorithm

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in {{ciphersuites}}.  Algorithm identifier
values are two octets long.

## DH-Based KEM

Suppose we are given a Diffie-Hellman group that provides the
following operations:

- GenerateKeyPair(): Generate an ephemeral key pair `(sk, pk)`
  for the DH group in use
- DH(sk, pk): Perform a non-interactive DH exchange using the
  private key sk and public key pk to produce a fixed-length shared
  secret
- Marshal(pk): Produce a fixed-length octet string encoding the
  public key `pk`
- Unmarshal(enc): Parse a fixed-length octet string to recover a
  public key

Then we can construct a KEM (which we'll call "DHKEM") in the
following way:

~~~
def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  zz = DH(skE, pkR)
  enc = Marshal(pkE)
  return zz, enc

def Decap(enc, skR):
  pkE = Unmarshal(enc)
  return DH(skR, pkE)

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  zz = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Marshal(pkE)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = Unmarshal(enc)
  return concat(DH(skR, pkE), DH(skR, pkS))
~~~

The GenerateKeyPair, Marshal, and Unmarshal functions are the same
as for the underlying DH group.  The Marshal functions for the
curves referenced in {#ciphersuites} are as follows:

* P-256: The X-coordinate of the point, encoded as a 32-octet
  big-endian integer
* P-521: The X-coordinate of the point, encoded as a 66-octet
  big-endian integer
* Curve25519: The standard 32-octet representation of the public key
* Curve448: The standard 56-octet representation of the public key

# Hybrid Public Key Encryption

In this section, we define a few HPKE variants.  All variants take a
recipient public key and a sequence of plaintexts `pt`, and produce an
encapsulated key `enc` and a sequence of ciphertexts `ct`.  These outputs are
constructed so that only the holder of the private key corresponding
to `pkR` can decapsulate the key from `enc` and decrypt the
ciphertexts.  All of the algorithms also take an `info` parameter
that can be used to influence the generation of keys (e.g., to fold
in identity information) and an `aad` parameter that provides
Additional Authenticated Data to the AEAD algorithm in use.

In addition to the base case of encrypting to a public key, we
include two authenticated variants, one of which authenticates
possession of a pre-shared key, and one of which authenticates
possession of a KEM private key.  The following one-octet values
will be used to distinguish between modes:

| Mode          | Value |
|:==============|:======|
| mode_base     | 0x00  |
| mode_psk      | 0x01  |
| mode_auth     | 0x02  |
| mode_auth_psk | 0x03  |

All of these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient
2. Use that context to encrypt or decrypt content

A "context" encodes the AEAD algorithm and key in use, and manages
the nonces used so that the same nonce is not used with multiple
plaintexts.

The constructions described here presume that the relevant non-private
parameters (`enc`, `pskID`, etc.) are transported between the sender and the
recipient by some application making use of HPKE.

The procedures described in this session are laid out in a
Python-like pseudocode.  The algorithms in use are left implicit.

## Creating the Encryption Context

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context. The key schedule inputs are as follows:

* `pkR` - The recipient's public key
* `zz` - A shared secret generated via the KEM for this transaction
* `enc` - An encapsulated key produced by the KEM for the recipient
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared secret held by both the sender
  and the recipient (optional; default value `zero(Nh)`).
* `pskID` - An identifier for the PSK (optional; default
  value `"" = zero(0)`
* `pkS` - The sender's public key (optional; default
  value `zero(Npk)`)

Senders and receivers MUST validate public keys for correctness.
For example, when using a DH-based KEM, the sender should check
that the receiver's key `pkR` is valid, i.e., a point on the
corresponding curve and part of the correct prime-order subgroup.
Similarly, the receiver should check that the sender's ephemeral
key `pkE` is valid. See {{kem-ids}} for discussion related to other KEMs.

The `psk` and `pskID` fields MUST appear together or not at all.
That is, if a non-default value is provided for one of them, then
the other MUST be set to a non-default value.

The key and nonce computed by this algorithm have the property that
they are only known to the holder of the recipient private key, and
the party that ran the KEM to generate `zz` and `enc`.  If the `psk`
and `pskID` arguments are provided, then the recipient is assured
that the sender held the PSK.  If the `pkSm` argument is
provided, then the recipient is assumed that the sender held the
corresponding private key (assuming that `zz` and `enc` were
generated using the AuthEncap / AuthDecap methods; see below).

The HPKE algorithm identifiers, i.e., the KEM `kem_id`, KDF `kdf_id`, and
AEAD `aead_id` 2-octet code points, are assumed implicit from the
implementation and not passed as parameters.

~~~~~
default_pkSm = zero(Npk)
default_psk = zero(Nh)
default_pskID = zero(0)

def VerifyMode(mode, psk, pskID, pkSm):
  got_psk = (psk != default_psk and pskID != default_pskID)
  no_psk = (psk == default_psk and pskID == default_pskID)
  got_pkSm = (pkSm != default_pkSm)
  no_pkSm = (pkSm == default_pkSm)

  if mode == mode_base and (got_psk or got_pkSm):
    raise Exception("Invalid configuration for mode_base")
  if mode == mode_psk and (no_psk or got_pkSm):
    raise Exception("Invalid configuration for mode_psk")
  if mode == mode_auth and (got_psk or no_pkSm):
    raise Exception("Invalid configuration for mode_auth")
  if mode == mode_auth_psk and (no_psk or no_pkSm):
    raise Exception("Invalid configuration for mode_auth_psk")

def KeySchedule(mode, pkR, zz, enc, info, psk, pskID, pkSm):
  VerifyMode(mode, psk, pskID, pkSm)

  pkRm = Marshal(pkR)
  ciphersuite = concat(kem_id, kdf_id, aead_id)
  pskID_hash = Hash(pskID)
  info_hash = Hash(info)
  context = concat(mode, ciphersuite, enc, pkRm, pkSm, pskID_hash, info_hash)

  secret = Extract(psk, zz)
  key = Expand(secret, concat("hpke key", context), Nk)
  nonce = Expand(secret, concat("hpke nonce", context), Nn)
  exporter_secret = Expand(secret, concat("hpke exp", context), Nh)

  return Context(key, nonce, exporter_secret)
~~~~~

Note that the context construction in the KeySchedule procedure is
equivalent to serializing a structure of the following form in the
TLS presentation syntax:

~~~~~
struct {
    // Mode and algorithms
    uint8 mode;
    uint16 kem_id;
    uint16 kdf_id;
    uint16 aead_id;

    // Public inputs to this key exchange
    opaque enc[Nenc];
    opaque pkR[Npk];
    opaque pkS[Npk];

    // Cryptographic hash of application-supplied pskID
    opaque pskID_hash[Nh];

    // Cryptographic hash of application-supplied info
    opaque info_hash[Nh];
} HPKEContext;
~~~~~

### Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
for the holder of a given KEM private key.  The `SetupBaseS()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The shared secret produced by the KEM is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

~~~~~
def SetupBaseS(pkR, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, pkR, zz, enc, info,
                          default_psk, default_pskID, default_pkSm)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, pk(skR), zz, enc, info,
                     default_psk, default_pskID, default_pkSm)
~~~~~

### Authentication using a Pre-Shared Key

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given pre-shared key
(PSK).  We assume that both parties have been provisioned with both
the PSK value `psk` and another octet string `pskID` that is used to
identify which PSK should be used.

The primary differences from the base case are:

* The PSK is used as the `salt` input to the KDF (instead of 0)
* The PSK ID is added to the context string used as the `info` input
  to the KDF

This mechanism is not suitable for use with a low-entropy password
as the PSK.  A malicious recipient that does not possess the PSK can
use decryption of a plaintext as an oracle for performing offline
dictionary attacks.

~~~~~
def SetupPSKS(pkR, info, psk, pskID):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_psk, pkR, zz, enc, info,
                          psk, pskSd, default_pkSm)

def SetupPSKR(enc, skR, info, psk, pskID):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, pk(skR), zz, enc, info,
                     psk, pskSd, default_pkSm)
~~~~~

### Authentication using an Asymmetric Key

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkS)` produces the correct shared secret
only if the encapsulated value `enc` was produced by
`AuthEncap(pkR, skS)`, where `skS` is the private key corresponding
to `pkS`.  In other words, only two people could have produced this
secret, so if the recipient is one, then the sender must be the
other.

The primary differences from the base case are:

* The calls to `Encap` and `Decap` are replaced with calls to
  `AuthEncap` and `AuthDecap`.
* The sender public key is added to the context string

Obviously, this variant can only be used with a KEM that provides
`AuthEncap()` and `AuthDecap()` procedures.

This mechanism authenticates only the key pair of the sender, not
any other identity.  If an application wishes to authenticate some
other identity for the sender (e.g., an email address or domain
name), then this identity should be included in the `info` parameter
to avoid unknown key share attacks.

~~~~~
def SetupAuthS(pkR, info, skS):
  zz, enc = AuthEncap(pkR, skS)
  pkSm = Marshal(pk(skS))
  return enc, KeySchedule(mode_auth, pkR, zz, enc, info,
                          default_psk, default_pskID, pkSm)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  pkSm = Marshal(pkS)
  return KeySchedule(mode_auth, pk(skR), zz, enc, info,
                     default_psk, default_pskID, pkSm)
~~~~~

### Authentication using both a PSK and an Asymmetric Key

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, pskID, skS):
  zz, enc = AuthEncap(pkR, skS)
  pkSm = Marshal(pk(skS))
  return enc, KeySchedule(mode_auth_psk, pkR, zz, enc, info,
                          psk, pskID, pkSm)

def SetupAuthPSKR(enc, skR, info, psk, pskID, pkS):
  zz = AuthDecap(enc, skR, pkS)
  pkSm = Marshal(pkS)
  return KeySchedule(mode_auth_psk, pk(skR), zz, enc, info,
                     psk, pskID, pkSm)
~~~~~

## Encryption and Decryption {#hpke-dem}

HPKE allows multiple encryption operations to be done based on a
given setup transaction.  Since the public-key operations involved
in setup are typically more expensive than symmetric encryption or
decryption, this allows applications to "amortize" the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this decryption must be
stateful. Each of the setup procedures above produces a context object
that stores the required state:

* The AEAD algorithm in use
* The key to be used with the AEAD algorithm
* A base nonce value
* A sequence number (initially 0)

All of these fields except the sequence number are constant.  The
sequence number is used to provide nonce uniqueness: The nonce used
for each encryption or decryption operation is the result of XORing
the base nonce with the current sequence number, encoded as a
big-endian integer of the same length as the nonce.  Implementations
MAY use a sequence number that is shorter than the nonce (padding on
the left with zero), but MUST return an error if the sequence number
overflows.

Encryption is unidirectional from sender to recipient. Each encryption
or decryption operation increments the sequence number for the context
in use.  The sender's context MUST be used for encryption only. Similarly,
the recipient's context MUST be used for decryption only. Higher-level
protocols re-using the HPKE key exchange for more general purposes can
derive separate keying material as needed using use the Export interface;
see {{hpke-export}} for more details.

It is up to the application to ensure that encryptions and
decryptions are done in the proper sequence, so that encryption
and decryption nonces align. If a Seal or Open operation would cause the `seq`
field to wrap, then the implementation MUST return an error.

~~~~~
def Context.Nonce(seq):
  encSeq = encode_big_endian(seq, len(self.nonce))
  return xor(self.nonce, encSeq)

def Context.IncrementSeq():
  if self.seq >= (1 << Nn) - 1:
    return NonceOverflowError
  self.seq += 1

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.Nonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.Nonce(self.seq), aad, ct)
  if pt == OpenError:
    return OpenError
  self.IncrementSeq()
  return pt
~~~~~

## Secret Export {#hpke-export}

HPKE provides a interface for exporting secrets from the encryption Context, similar
to the TLS 1.3 exporter interface (See {{?RFC8446}}, Section 7.5). This interface takes as
input a context string `exporter_context` and desired length `L` (in octets), and produces
a secret derived from the internal exporter secret using the corresponding KDF Expand
function.

~~~~~
def Context.Export(exporter_context, L):
  return Expand(self.exporter_secret, exporter_context, L)
~~~~~

# Single-Shot APIs

In many cases, applications encrypt only a single message to a recipient's public key.
This section provides templates for HPKE APIs that implement stateless "single-shot" encryption
and decryption using APIs specified in {{hpke-kem}} and {{hpke-dem}}:

~~~~~
def Seal<MODE>(pkR, info, aad, pt, ...):
  enc, ctx = Setup<MODE>I(pkR, info, ...)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def Open<MODE>(enc, skR, info, aad, ct, ...):
  ctx = Setup<MODE>R(enc, skR, info, ...)
  return ctx.Open(aad, ct)
~~~~~

The `MODE` template parameter is one of Base, PSK, Auth, or AuthPSK. The optional parameters
indicated by "..."" depend on `MODE` and may be empty. SetupBase, for example, has no
additional parameters. Thus, SealAuthPSK and OpenAuthPSK would be implemented as follows:

~~~
def SealAuthPSK(pkR, info, aad, pt, psk, pskID, skS):
  enc, ctx = SetupAuthPSKS(pkR, info, psk, pskID, skS)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def OpenAuthPSK(enc, skR, info, aad, ct, psk, pskID, pkS):
  ctx = SetupAuthPSKR(enc, skR, info, psk, pskID, pkS)
  return ctx.Open(aad, ct)
~~~

# Algorithm Identifiers {#ciphersuites}

## Key Encapsulation Mechanisms (KEMs) {#kem-ids}

| Value  | KEM               | Nenc | Npk | Reference      |
|:-------|:------------------|:-----|:----|:---------------|
| 0x0000 | (reserved)        | N/A  | N/A | N/A            |
| 0x0010 | DHKEM(P-256)      | 32   | 32  | {{NISTCurves}} |
| 0x0011 | DHKEM(P-384)      | 48   | 48  | {{NISTCurves}} |
| 0x0012 | DHKEM(P-521)      | 65   | 65  | {{NISTCurves}} |
| 0x0020 | DHKEM(Curve25519) | 32   | 32  | {{?RFC7748}}   |
| 0x0021 | DHKEM(Curve448)   | 56   | 56  | {{?RFC7748}}   |

For the NIST curves P-256 and P-521, the Marshal function of the DH
scheme produces the normal (non-compressed) representation of the
public key, according to {{SECG}}.  When these curves are used, the
recipient of an HPKE ciphertext MUST validate that the ephemeral public
key `pkE` is on the curve.  The relevant validation procedures are
defined in {{keyagreement}}.

For the CFRG curves Curve25519 and Curve448, the Marshal function is
the identity function, since these curves already use fixed-length
octet strings for public keys.

## Key Derivation Functions (KDFs) {#kdf-ids}

| Value  | KDF         | Nh  | Reference    |
|:-------|:------------|-----|:-------------|
| 0x0000 | (reserved)  | N/A | N/A          |
| 0x0001 | HKDF-SHA256 | 32  | {{?RFC5869}} |
| 0x0002 | HKDF-SHA384 | 48  | {{?RFC5869}} |
| 0x0003 | HKDF-SHA512 | 64  | {{?RFC5869}} |

## Authenticated Encryption with Associated Data (AEAD) Functions {#aead-ids}

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-GCM-128      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-GCM-256      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |

# Security Considerations

The general security properties of HPKE are described in
{{security-properties}}.  In this section, we consider a security issue that may
arise in practice and an advanced use case.

## External Requirements / Non-Goals

HPKE is designed to be a fairly low-level primitive, and thus does not provide
several features that a more high-level protocol might provide, for example:

* Downgrade prevention - HPKE assumes that the sender and recipient agree on
  what algorithms to use.  Depending on how these algorithms are negotiated, it
  may be possible for an intermediary to force the two parties to use
  suboptimal algorithms.

* Replay protection - The requirement that ciphertexts be presented to the
  Context.Open function in the same order they were generated by Context.Seal
  provides a degree of replay protection within a stream of ciphertexts
  resulting from a given Context.  HPKE provides no other replay protection.

* Forward secrecy - HPKE ciphertexts are not forward-secure. In mode_base
  and mode_auth, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In mode_psk and mode_auth_psk, a given
  ciphertext can be decrypted if the recipient's public encryption key and the
  PSK are compromised.

## Metadata Protection

The authenticated modes of HPKE (PSK, Auth, AuthPSK) require that the recipient
know what key material to use for the sender.  This can be signaled in
applications by sending the PSK ID (`pskID` above) and/or the sender's public
key (`pkS`).  However, these values themselves might be considered sensitive,
since in a given application context, they might identify the sender.

An application that wishes to protect these metadata values without requiring
further provisioning of keys can use an additional instance of HPKE, using the
unauthenticated base mode.  Where the application might have sent `(pskID, pkS,
enc, ciphertext)` before, it would now send (enc2, ciphertext2, enc, ciphertext),
where `(enc2, ciphertext2)` represent the encryption of the `pskID` and `pkS`
values.

The cost of this approach is an additional KEM operation each for the sender and
the recipient.  A potential lower-cost approach (involving only symmetric
operations) would be available if the nonce-protection schemes in {{BNT19}}
could be extended to cover other metadata.  However, this construction would
require further analysis.

## Designated-Verifier Signature

The Auth and AuthPSK modes HPKE can be used to construct a lightweight
"designated-verifier signature" scheme {{JKR96}}, in the sense that the message
is authenticated as coming from the sender, but the only party who can verify
the authentication is the recipient (the holder of `skR`).

To create such a signature, the sender simply performs a normal HPKE setup in
the proper mode, and calls the Seal method on the resulting context with an
empty plaintext value and the content to be signed as AAD.  This produces an
encoded key `enc` and a ciphertext value that contains only the AAD tag.

For example, using DHKEM-X25519 and AES-128-GCM, this would produce a 48-byte
signature comprising a 32-byte ephemeral X25519 key and a 16-byte GCM tag.

To verify such a signature, the recipient performs the corresponding HPKE setup
and calls Open with the provided ciphertext.  If the AEAD authentication passes,
then the signature is valid.

This scheme re-uses the authentication scheme underlying the AEAD algorithm in
use, while using the KEM to establish a one-time authentication key from a pair
of KEM public keys.

# Message Encoding

This document does not specify a wire format encoding for HPKE messages. Applications
that adopt HPKE must therefore specify an unambiguous encoding mechanism which includes,
minimally: the encapsulated value `enc`, ciphertext value(s) (and order if there are
multiple), and any info values that are not implicit.

# IANA Considerations

This document requests the creation of three new IANA registries:

* HPKE KEM Identifiers
* HPKE KDF Identifiers
* HPKE AEAD Identifiers

All of these registries should be under a heading of "Hybrid Public Key
Encryption", and administered under a Specification Required policy {{!RFC8126}}

## KEM Identifiers

The "HPKE KEM Identifiers" registry lists identifiers for key encapsulation
algorithms defined for use with HPKE.  These are two-byte values, so the
maximum possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KEM: The name of the algorithm
* Nenc: The length in bytes of an encapsulated key produced by the algorithm
* Npk: The length in bytes of a public key for the algorithm
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kem-ids}}

## KDF Identifiers

The "HPKE KDF Identifiers" registry lists identifiers for key derivation
functions defined for use with HPKE.  These are two-byte values, so the maximum
possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KDF: The name of the algorithm
* Nh: The length in bytes of the output of the KDF
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kdf-ids}}

## AEAD Identifiers

The "HPKE AEAD Identifiers" registry lists identifiers for authenticated
encryption with associated data (AEAD) algorithms defined for use with HPKE.
These are two-byte values, so the maximum possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* AEAD: The name of the algorithm
* Nk: The length in bytes of a key for this algorithm
* Nn: The length in bytes of a nonce for this algorithm
* Reference: Where this algorithm is defined

Initial contents: Provided in {{aead-ids}}

--- back

# Test Vectors

These test vectors are also available in JSON format at {{TestVectors}}.

## DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128

### PSK Setup Information
~~~
mode: 1
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 5ce36cd4c5af3ed83e014e38e7ad0ec2312e9aeaeac4934f9faa94f37c510a14
skS: e2540736419e750be7fef884281a0ceb27eb55f015be6a8b98394b05e1f835c1
skE: e3020ce69c51d9ce0313c02c378060b3dccf764c774745ccc19d5f329d857ca3
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 29ed07fa1a6ae22a58fd363a59b75489984c06d0f5028d09822ec5abec23bc3b
pkS: 97c5073c23d9f4a2a257f58d175951c0bedd4cd275dc8e482fd283f96f1ee968
pkE: 71a32b96444b485d59f951ac59b4947a49b83495f1096698e19e8bf894a1a619
enc: 71a32b96444b485d59f951ac59b4947a49b83495f1096698e19e8bf894a1a619
zz: ed3e93b4c4f23dc50c0f09aa69afa79a3702de035dee3b34355168cae7814b69
context: 0100020001000171a32b96444b485d59f951ac59b4947a49b83495f1096698e
19e8bf894a1a61929ed07fa1a6ae22a58fd363a59b75489984c06d0f5028d09822ec5abe
c23bc3b0000000000000000000000000000000000000000000000000000000000000000e
ca994d516108a16db86e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: 9f413dd1fc5fc3480dd1efd45264fad715dc088c082de893c16dd230acab3c37
key: 166aa4e4646c130ce9e821f908840af5
nonce: f1dc8d9393cb70265cb0b67b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f1dc8d9393cb70265cb0b67b
ciphertext: 9841fde671d4a5f15db6bce37eaf8104eda0c1b1c76fb0e1c2d62c034527
238d63080db5de07c5964a102850fd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f1dc8d9393cb70265cb0b67a
ciphertext: 42a0edb84f43a1560ea1b85272feec5b4ef1e50cebaef918d44863d72267
eb5e574b05cfc01fb6c432949665d5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f1dc8d9393cb70265cb0b679
ciphertext: 91e4cc408ed83b7e8c8f87877a74997b4d6dd435f18522bcb7ebdbe479a4
356cc8f05d43c54d46bbb23edd29c8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f1dc8d9393cb70265cb0b67f
ciphertext: 9f20f4d762294aa7eb179273f11b20b2fdb2405754ee455826ce41935950
e14d3413644676bb3683dd1db0c4a2

~~~

## DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128

### Auth Setup Information
~~~
mode: 2
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 17b41067f7029b74dc18ec3cd5b42a046fbbcc891c7a377522add7732d8c7f36
skS: e69cd206458d650207cb32df70ec05d62b8b5e65ac00f57e5cb074200d94d95c
skE: 8760b1a25cfb4d6b09a32a9195f4c8035d3746cf08bcf41fe9e7d8f22cddbd5e
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 14f5da85361a18797e161eda6403da8ab9eddb92dfba11365cd5ef61cab5730f
pkS: 05e5d4ca870f5a492e1b3675b7699648eea77125894b0b375fef58cdde258d30
pkE: 545a3d23e069392a53590891cc4088251942ef21ecb4612d071cbe55a26fa321
enc: 545a3d23e069392a53590891cc4088251942ef21ecb4612d071cbe55a26fa321
zz: 96436cf588675a012ff3c2b072179be1b75fee306e65c4aafcf894515cd6ad3555e1
ab3ccf68b07310b45523c12f93640762388e9baa7f38cf660a4a9cb9270c
context: 02000200010001545a3d23e069392a53590891cc4088251942ef21ecb4612d0
71cbe55a26fa32114f5da85361a18797e161eda6403da8ab9eddb92dfba11365cd5ef61c
ab5730f05e5d4ca870f5a492e1b3675b7699648eea77125894b0b375fef58cdde258d30e
3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b85555c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: a52b9dbdfbfc6ed1f1e89297e241494803ec101d1239f6f5a232720d0aafc4f7
key: 6ea76af9e2ea2b438d022fd4519a2e3a
nonce: 65f13121b6837d415fc5ffff
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 65f13121b6837d415fc5ffff
ciphertext: 129c6491e5b92b7fd118d0f710e1006fb9201622c6d499d8925188fbeebc
17d232b273ea26c2730f971cd07b6d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 65f13121b6837d415fc5fffe
ciphertext: 8dc12ea8f1f8831f0a22ea6e46f94c756d17c421d5e509177858fb507655
cd4cd47f1a6ec8dcc112dd2e703622

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 65f13121b6837d415fc5fffd
ciphertext: d1dd126505f6f3ce9d8972a4fca9675d28612889ca68db023330fbed6adb
9206d10a68c2af7382bc3ff347c337

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 65f13121b6837d415fc5fffb
ciphertext: ac66db553712823557aaa1d66aeda4831b0bda70d590f4f080b043432d64
ae38838f83c2356191da0d56b8c3ae

~~~

## DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128

### AuthPSK Setup Information
~~~
mode: 3
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 961dcd519bc684244c6a6a3452b43246005ecc890bc47271d35a8991830c94f8
skS: 64a5c87a8fbfdfaf5f5c518f1a052c1474e328cd40fa5982abf9932cea93e893
skE: c8b9d2dc75ff6645c7fc8a31a24f917681bd58d7797cd1ae85a6f99f404af4a5
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 9947b6c5591b5099e1e9b04e14dc8700fa10c26629da306de31fc283969ea343
pkS: 4e601dabf5c197fef0823add2b76cc28933f1c868fc5607da4cab44d504f4c4e
pkE: 5ea5c1184c9cfe7e077791d650f876cb97117d69307fea6700a7d1024726722e
enc: 5ea5c1184c9cfe7e077791d650f876cb97117d69307fea6700a7d1024726722e
zz: e02201d6d2e1cd668ec39022054dbec949e3ce747056b4470d3d06a61c7d65622f52
2afed540081e32e61106559008443a8e7a58936d09db988f5411a4c2ee76
context: 030002000100015ea5c1184c9cfe7e077791d650f876cb97117d69307fea670
0a7d1024726722e9947b6c5591b5099e1e9b04e14dc8700fa10c26629da306de31fc2839
69ea3434e601dabf5c197fef0823add2b76cc28933f1c868fc5607da4cab44d504f4c4ee
ca994d516108a16db86e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: 915960a170567b352eaa945f189dc00cb859f50d6db1bf3baa5fcc8828f8c2c4
key: 791068a6ed49b0a16801bfcf4c7b35c0
nonce: 8d5663bfe2f24f6f9d1a7b0b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8d5663bfe2f24f6f9d1a7b0b
ciphertext: 3136dcdee0991b1d18bd1618cdba690a6cf30516af5dd0d21fa35d57e59d
860955fe2676fd82755b32ea50cde1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8d5663bfe2f24f6f9d1a7b0a
ciphertext: 913e3ff37113f2143f1c54a78af62b61f6ddec52d43482f25f3353d74e03
52863afacdd9cd5ae34103aa8b2554

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8d5663bfe2f24f6f9d1a7b09
ciphertext: e0bf438684af99d957aa954664a92abc13ff392c19b50920280aca30a65e
8a2ea4d88d1b7a436d269fe06243b3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8d5663bfe2f24f6f9d1a7b0f
ciphertext: 56ff0175d8f841557d9984bd01d5f97280eae1afd0f6c1ebef6f86e87f62
a9218943588fba85d6832d2c970e9e

~~~

## DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2c03c3b928fa93475bf78e68537ca60a228ad24c2c2da1287467de6dd494f429
skS: d109522320079b7cba1b0cc12642ba5e5d663b8d0b36a182f35b7c8c71644d0e
skE: e36928314c9cad618db3e2876501497b2fdd0dc199d77ed94a51de81bff182e8
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 74db4416e5a3ecd24f999c457fce1c86f14f90060efd1fcc413c28d16ccc3344
pkS: 28ea71496f541782c2aa4ad9e62e6431ef0ed5aa1b6c3c97088c117bf1f1d20b
pkE: a4265bc60efeca25549f0534cfea14e92d29c34a3edb90334ff9efd2bcdfa342
enc: a4265bc60efeca25549f0534cfea14e92d29c34a3edb90334ff9efd2bcdfa342
zz: 3dca7ddff43c7c316aaef4ef2f5d9f9bee6cf39739bba709a25f45725d749c5a
context: 00000200010001a4265bc60efeca25549f0534cfea14e92d29c34a3edb90334
ff9efd2bcdfa34274db4416e5a3ecd24f999c457fce1c86f14f90060efd1fcc413c28d16
ccc33440000000000000000000000000000000000000000000000000000000000000000e
3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b85555c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: f4f90b507e2a9257441afe94c4107243187b37adab35aca399b451f56647c458
key: 521ffa3f12fb96bd825e0fdd1fc984f0
nonce: 4eeba357516d210473faa4c9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4eeba357516d210473faa4c9
ciphertext: b890b7b63836ec816f3661e6947668e33fddec31fa8f9d04cb8f88147e03
fd6e0db045705aae4154e2b11959e1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4eeba357516d210473faa4c8
ciphertext: 44f848a21c4b85450717324a3a3278cb98e38083d5cf06aae5394df69361
b9b34323fcf057fe9ca992c8be229c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4eeba357516d210473faa4cb
ciphertext: b0c6d9c76d8e5b411f6f4031ad2c340f2979973548c5b80d1a57cca875fe
4cdf7c07bd26d17f18785b4569295d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4eeba357516d210473faa4cd
ciphertext: f7b8e1f6d0b2db6e533b9063c878fbf021191bc251727b550285e00530d3
cf883f536c6d3337cb536de58547f5

~~~

## DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 38cd8838163f5b9c2d32056837b2df02a54c16a57e8e1ada58a82c37b9f00dcc
skS: 9623e6b76b431184904b9a4c9b2594c5979348e260bb956d135c0604dcf064fa
skE: 14747bd0f0642e0f9da09a3b347ea080102b6d4be7f7d24cb06695684279844f
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040b6d97479077984cf50615f670e7008ddf85aa9f6ce195a0ed5549f5f99d25c0a
4687715056e343f0785282ff00edb1674e813e27e37b85cc038424346b3af6c
pkS: 046f5bba051d505fe62f36402a5b92ecf6e4f81fd393b8731ad03e2bdc9920fbf53
dad8710b20ff1a1f32ef63b22cfa8cd26bdb70f1b4b2df68af7edf56e3c7cda
pkE: 04642a43790930644479a044cb769a0c1fb1ec3552004c7d12eaa74e82f5ff59e8e
2b9553ab89c45ee17cb831f54a955f38bf19666e942dbe62b9128b24b45d465
enc: 04642a43790930644479a044cb769a0c1fb1ec3552004c7d12eaa74e82f5ff59e8e
2b9553ab89c45ee17cb831f54a955f38bf19666e942dbe62b9128b24b45d465
zz: 5f443760b24d90ad460b70d6647fc37603c6442c2d35ce1c21b97d6f3c237b60
context: 0000010001000304642a43790930644479a044cb769a0c1fb1ec3552004c7d1
2eaa74e82f5ff59e8e2b9553ab89c45ee17cb831f54a955f38bf19666e942dbe62b9128b
24b45d465040b6d97479077984cf50615f670e7008ddf85aa9f6ce195a0ed5549f5f99d2
5c0a4687715056e343f0785282ff00edb1674e813e27e37b85cc038424346b3af6c00000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000e3b0c44298fc1c149af
bf4c8996fb92427ae41e4649b934ca495991b7852b85555c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 54fc4d2a8a73415cf572646f7b35b60295def16b38001df990aeba96aa9385c4
key: 8df36a3b2d9efd8014e78f6db1d80a35b267253fb596915dc927faef288a851c
nonce: d87f49d856e9656f98f41e49
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d87f49d856e9656f98f41e49
ciphertext: baf88db06447f314b3a56d2bdb3574e4db08a54cc18c03eef367ccc7f201
15147d9dbee57c4a455ac4131dd927

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d87f49d856e9656f98f41e48
ciphertext: 0acff42705e3fe0e443cdca510e1030f6f8d8ba2ccc823d6980472dd2c50
e8a520dbd7f94fe8f7a1e3778f0d2a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d87f49d856e9656f98f41e4b
ciphertext: 01059b1632304feafbd606f96e727fc249030a551939519457d44a965325
e9edabbf8d554d0681a9a79d2d2b8a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d87f49d856e9656f98f41e4d
ciphertext: 4e6d499d025ef198090527d25779ab18644ec7845c2a6033d1de5ce49cca
293dcad7b1d2448474c91cdf612844

~~~

## DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305

### PSK Setup Information
~~~
mode: 1
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: e5e343bab850d17bf25a3d69a986c2954eb466ba2b2962fea121c3710283b011
skS: 1fbdbe48a4bbf6d64dbdd5165fdbc37f08d1b4186b8ddebcdec60dd33db43557
skE: ec43ac2b9d72a1d3c4d7e3ca68088452a0b37004fb47f2fc5177364a2595a482
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0407e36376e26612997f9ca72e3e1512cad6ac794e35a665e1459234d1eb0e4b7ed
6196ca9925fb42eb426b796db3efea5510ac9bd8a801b283a5ce8f8cacfa30b
pkS: 0447c25cdaabc23d526465a76e5f77acbb12acd5262942be60fc3932ee0b1ba6ebb
832392a559dde3a925b4d297372f4e582336809b63f151acfd2c2c6b7f445f9
pkE: 0454f521fa24c53c31b0bc7d54a4d14867ab36025e3737222babf1d54eff1b13db7
2275bc2cb2d3114aaabc904ff3823c40e7ac7bea3605cb99dc5292105a6a51c
enc: 0454f521fa24c53c31b0bc7d54a4d14867ab36025e3737222babf1d54eff1b13db7
2275bc2cb2d3114aaabc904ff3823c40e7ac7bea3605cb99dc5292105a6a51c
zz: f99a0a5ffd68c2108ab238cac30ed565b87ddca9e7a073495bcc5f945c226b72
context: 010001000100030454f521fa24c53c31b0bc7d54a4d14867ab36025e3737222
babf1d54eff1b13db72275bc2cb2d3114aaabc904ff3823c40e7ac7bea3605cb99dc5292
105a6a51c0407e36376e26612997f9ca72e3e1512cad6ac794e35a665e1459234d1eb0e4
b7ed6196ca9925fb42eb426b796db3efea5510ac9bd8a801b283a5ce8f8cacfa30b00000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000eca994d516108a16db8
6e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: de479ec4061a3fe0f3e0f24fcecc819307eca848aacb812b482c061c7d630d44
key: 874b2ae514e49687f7f23e5886b3157d598cb075a6a8cbcebca85f63090e7e6f
nonce: 14ec3c2b9e8247560709bbf6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 14ec3c2b9e8247560709bbf6
ciphertext: a2a4e5ab0dcad7464e72f754e7423ddb46ec31d62f216ffe0675ef388b17
09bfb50736e5cf39bc49a75d837e88

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 14ec3c2b9e8247560709bbf7
ciphertext: 43bdcc7e2b29706a4f8e460adef4edb085b8efc10771f187fac5e4e679d0
4f6990796d76ad1062f815f36ba584

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 14ec3c2b9e8247560709bbf4
ciphertext: 9b5853d35974cbd2e57adb4549e2f401737f9f31c808f3c5a59d81a30b8a
77f034ff4dc7f1062036485bc4af0d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 14ec3c2b9e8247560709bbf2
ciphertext: 9b78fad36cda2746fcb71bdc4d7ea249738ae449f074bc8dab43e83fabf3
f9bf7030b79a50192ff48222baacf5

~~~

## DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305

### Auth Setup Information
~~~
mode: 2
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: e74aa33846ed01f498b0dd8f0a5275b854765d9d83cdef8c1eb0a3c2172f2bab
skS: b3b16a2b618acb9752155760882646cc9a8d4abd239ad84e31cb8a8fc8c55961
skE: 1ae64a66b19847d62c267e5c2c94b71d734da83eec54d14bf893e1000a1ef862
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04646dad58c1ed265fc56416cbfc91a387b34579efc7e8e10f7f86e509a202abcfe
f5f119acc3c8465d2f2e19944b618bfbf5388637e4ad28643c2623419d1bc75
pkS: 04233f9d83799e9c4ddea37c4fcbd97fd4f7740731f0d100e5535cac2d68f5aa3f8
62acf90c948e48357d8c358536eb70500f90e0631a8102ae9f4054609ca008c
pkE: 047f2e7b859e82278e5b90acb35dcd51e630c1a2b59b90ed5dd9af4b2d2138316ae
9e9a54f05405efc44b80a94c4c0fa974f685dcac7870c718c5001ce519a5208
enc: 047f2e7b859e82278e5b90acb35dcd51e630c1a2b59b90ed5dd9af4b2d2138316ae
9e9a54f05405efc44b80a94c4c0fa974f685dcac7870c718c5001ce519a5208
zz: 6b4d69710007ef44805c2ad70b7714c19e149056c7f2fc6070069fb35cdd3f213e7b
be56c0c6e21561f4ffa6d26887fb8e2a8534bf2ac30c1858709b249c0184
context: 02000100010003047f2e7b859e82278e5b90acb35dcd51e630c1a2b59b90ed5
dd9af4b2d2138316ae9e9a54f05405efc44b80a94c4c0fa974f685dcac7870c718c5001c
e519a520804646dad58c1ed265fc56416cbfc91a387b34579efc7e8e10f7f86e509a202a
bcfef5f119acc3c8465d2f2e19944b618bfbf5388637e4ad28643c2623419d1bc7504233
f9d83799e9c4ddea37c4fcbd97fd4f7740731f0d100e5535cac2d68f5aa3f862acf90c94
8e48357d8c358536eb70500f90e0631a8102ae9f4054609ca008ce3b0c44298fc1c149af
bf4c8996fb92427ae41e4649b934ca495991b7852b85555c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 8ed56ce744227619de1f23d31a1c91015d7d187b3eb59b63126419acb6135151
key: 39bd7d22903208f5723f2ada027ca4b5059af0a73992bad0945d10b693ff7693
nonce: 93ef2e83ad85efae83d594b0
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 93ef2e83ad85efae83d594b0
ciphertext: bd3b945359046ea183b4b72942731821f445e98fc019188b6df10a4cbe7a
bb85383b7da3b26fa027f2a369038c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 93ef2e83ad85efae83d594b1
ciphertext: 6098208ce06ea0961f3f5fa6fe61d75ab28aefb3e0b86389a2922d694fd9
f298715d109d8caf14543535953748

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 93ef2e83ad85efae83d594b2
ciphertext: f4d2edfa80d00daf88406d269f9494668c488afc22305880eca89d222341
f814aa49fa11703d11465893c81ea7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 93ef2e83ad85efae83d594b4
ciphertext: acbe483f707cbd5b814ef833a1346c81e0158fe8e910b3386c7f46bbd064
8936f6a878d6c5fb8ada337d432d49

~~~

## DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305

### AuthPSK Setup Information
~~~
mode: 3
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: ae95cd69e719ec38d968db174f0c1dd4b3e8bc04b778222c5128f5532bf1bcd0
skS: 6bbc854ccdd54efe71bcf10d79c2244d6a7c7784568352a9e7dbe7fb77642340
skE: 29cb10f4e85542cdcbfb129cff73402fe2acb07b882372707aa212f4c1345278
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04e18a04b85490821f1386c3791c44d396aa8ceae787f6804bce1a9edd3288eb86c
3447072569f2ac025b2a745e338df4badee49c89b56b5556fdf0491341e6a45
pkS: 043e10a446394ce3a130c7421f869a26c55532e80c25422995abec3fd25c8ff0d15
f9a0d6d6c9061c185f7b2404736d6e9aa7626ec02f8ace743f46608fdc9a525
pkE: 04af75f7ee9e9b2fb213338a499909b7b0371199b6f95daf1261656a51b17766aad
1e6086215f9014a253f34eed77f30a9fc1eee7b66332728064cbdac656c9fec
enc: 04af75f7ee9e9b2fb213338a499909b7b0371199b6f95daf1261656a51b17766aad
1e6086215f9014a253f34eed77f30a9fc1eee7b66332728064cbdac656c9fec
zz: cb3984234d2d9d590907c4cb6fefc8292a99975a0695e462d7e20807f169537867d3
7ef4a747408c2c5b82bd848f421cd5453d7b09243550ba47ea1e8b8b7ad2
context: 0300010001000304af75f7ee9e9b2fb213338a499909b7b0371199b6f95daf1
261656a51b17766aad1e6086215f9014a253f34eed77f30a9fc1eee7b66332728064cbda
c656c9fec04e18a04b85490821f1386c3791c44d396aa8ceae787f6804bce1a9edd3288e
b86c3447072569f2ac025b2a745e338df4badee49c89b56b5556fdf0491341e6a45043e1
0a446394ce3a130c7421f869a26c55532e80c25422995abec3fd25c8ff0d15f9a0d6d6c9
061c185f7b2404736d6e9aa7626ec02f8ace743f46608fdc9a525eca994d516108a16db8
6e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: b9e7d191bc07176931b5da907f252e6541778234fbc2ed8c6c83e0d53bcf666f
key: 19102b587932782513b20cfa23ddbae332eae9d1ab0f827203798e6b1ea27227
nonce: 24699a2786e6029483f5a241
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 24699a2786e6029483f5a241
ciphertext: 30888469bf1806322030d883444e9faf1790b93437274918f081c16ae101
6adcb880c8d14a9d6be22770375373

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 24699a2786e6029483f5a240
ciphertext: 0fa6d8d3711cb2c44ec3c6d284c1ec84af0da7d82e37809d76de2bb10a7d
721bee730af70867922d1f7abf2be1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 24699a2786e6029483f5a243
ciphertext: 280dacb25ee1aeda332cc43eb7c7bb58519a3aea0049ab0e0041d488cae3
ce41653cac5f062abf33a51c98fb3a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 24699a2786e6029483f5a245
ciphertext: aba3d64475c658bc312820605d85b901f185ca898f1f2905210b72972441
aea47a87b56e76b278e6f045b5c2e3

~~~

## DHKEM(P-521), HKDF-SHA512, AES-GCM-256

### Auth Setup Information
~~~
mode: 2
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 008081c311f5de8d8a785d8bb5250cc912e33867e60e30770c6fce5700b4f10ef33
c25bc52da31e9da759ba8fccd518d1620a9aa44457c45b2d26ee0114ccc98db6f
skS: 0073b373526cea2a50f17e15a7c6fc801e6efcdff78166e492bf5ceb834fbbb9a3b
87df4998af53be985c8492e9ced5692930cb850751858f4412e8ce4a139437413
skE: 006552858884fa2cdd51a6cb71ce8fc59f7a95ee9a8aade84689d53fc44d98fc025
f0035564c614001c1e5bc8e53f421b68a1908d51263e24a1240676c12ff0f50d9
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04006ade48e3284dfd057f83f86bca3781671395ba8058ab11f728a781c5e829de9
3011477b16059a4412a43b14d0d3b223a2b0dfcc0f7e10ab422bc6a852a9ebd9f180151d
38dcd87e75a36788184df8edbc64136c1a1e1dc8fbe56def5aea2a8e90ff70e9f0a7f965
ccdd0a562059864b1184cd4480256863db90ff3c039695b5d483b75
pkS: 040010b3ee6721d7760b5e1d3b2408eea04e2330ca89980bd4ea30fe9e4d9caf385
eb9a40d83abb7004c2a089e9cfe5988e673bab1033a1e07e93b6c3eca9f39390faa00ac1
9448ad46030cb9262372bf40f765569e827cc22f4c09016459f91829694d3074cb1144ed
f3532b8835cbf58d66a5b546c90eac75668460d1e2326fcf2826405
pkE: 0401bd2c9b22733323343506717399efa67a9fe9f0ae4e0484ecf37a990cf70957a
39572f6ec93adf293d2e64eb783846bc83f4e18a0f7a7bf5293e83b3fa3ebf05c9501ff2
278679ac7384e9ac20fe22d20d456e9faa078efd65ed3e217975e21bde9d199d26e7754a
5f8542bea29cf26309ac4774449364e58e2047eb0dc95886bb0d9b8
enc: 0401bd2c9b22733323343506717399efa67a9fe9f0ae4e0484ecf37a990cf70957a
39572f6ec93adf293d2e64eb783846bc83f4e18a0f7a7bf5293e83b3fa3ebf05c9501ff2
278679ac7384e9ac20fe22d20d456e9faa078efd65ed3e217975e21bde9d199d26e7754a
5f8542bea29cf26309ac4774449364e58e2047eb0dc95886bb0d9b8
zz: 016b09b1a6ab41a974d4d0f201359c16eb6e36576b5d955e6e3f7fa5cd55039c992e
eba24996e278c698409ffeb4f56db255d5bbf32e8cad1e25a1c63b6dc7431478006c817a
932e5b571bcd4b488068995a2bc2768afcc17120991fe458015286beb7f9a0f379b6bf47
a30bccafa25deb783e777adbfe4abb8e03de76deaec565f89722
context: 020003000200020401bd2c9b22733323343506717399efa67a9fe9f0ae4e048
4ecf37a990cf70957a39572f6ec93adf293d2e64eb783846bc83f4e18a0f7a7bf5293e83
b3fa3ebf05c9501ff2278679ac7384e9ac20fe22d20d456e9faa078efd65ed3e217975e2
1bde9d199d26e7754a5f8542bea29cf26309ac4774449364e58e2047eb0dc95886bb0d9b
804006ade48e3284dfd057f83f86bca3781671395ba8058ab11f728a781c5e829de93011
477b16059a4412a43b14d0d3b223a2b0dfcc0f7e10ab422bc6a852a9ebd9f180151d38dc
d87e75a36788184df8edbc64136c1a1e1dc8fbe56def5aea2a8e90ff70e9f0a7f965ccdd
0a562059864b1184cd4480256863db90ff3c039695b5d483b75040010b3ee6721d7760b5
e1d3b2408eea04e2330ca89980bd4ea30fe9e4d9caf385eb9a40d83abb7004c2a089e9cf
e5988e673bab1033a1e07e93b6c3eca9f39390faa00ac19448ad46030cb9262372bf40f7
65569e827cc22f4c09016459f91829694d3074cb1144edf3532b8835cbf58d66a5b546c9
0eac75668460d1e2326fcf2826405cf83e1357eefb8bdf1542850d66d8007d620e4050b5
715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a53
8327af927da3e490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: cd34e00832d73a6316bbf3bc517706d2a6c41ac3c7b5465c9619c4d9bbd56046
533b16ed57ac580e844bf426c13e3112ebcb3b3671d64202dbf58251d1a9bac8
key: 30073110503c9a1ee720d9a488ff05af2fbe1f8c5b993d4e3e6b96acb1d1fa38
nonce: fedd44845e091206dd2adcf3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: fedd44845e091206dd2adcf3
ciphertext: c933e934599b93418fb7d0decb609dbd3d7c0a9b4f0fb63af315f5de3be7
a6e375895344b7589a99782f11b698

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: fedd44845e091206dd2adcf2
ciphertext: 58b9c9c9f37703ade2180ae29309268a938f5daf2f18ad98cbff37cd48d6
8be177f1105577e9ec1c80f49f7a8b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: fedd44845e091206dd2adcf1
ciphertext: 198147c34b091179f59858a3ba67c98c67129fba79d245fc76a92f1c6ec0
8632d6d994db37436b240f7e14127f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: fedd44845e091206dd2adcf7
ciphertext: 4f170e1ad48b5be8122edd89a39eaf737ec1c8485bb7374a840191d3a759
2566a8dadb442f19a9d2d292c8a736

~~~

## DHKEM(P-521), HKDF-SHA512, AES-GCM-256

### AuthPSK Setup Information
~~~
mode: 3
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0039bfdf6630a385917af8da9ba104c99f25546bbcb684f517024d60d19a7233019
ec7a12634ba493001ec36fe73ecdabf88c036feb03efffc32119323d2f1f4aca6
skS: 00a8b0dd9f104a78d3b847d3c28009194bd93eaa8269d7086c8c4112effbfe539e8
32eb377eeb277074dc25e97b99d326ab67aff2188c36af92075d6ade33f8300ed
skE: 00a247923e82c677ccfec84a3b9a6d2496be9cef672c6a80142e29da55b0acc45d4
2faee929847b14d0e30dfb8ba236fd3846e628cf37decf48d6888e49e110bda82
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04012c3c8145099336bc8c2839c5f2a846f38864b2d00d82a7d508e939affa0b994
780125498a76ec7c9956784e00c249f0811794750722561e571f32879689d87883001794
3ffae1d4b71bfe0bc211ef13e0cee99cd83518ab1fbfb5c26fcb7339810033304458b92a
eb56fa5c4f3808023c0ea872e5bb1d8299f9ae68187c0667278bfce
pkS: 0401a762534eac8a21420a6801d050a3d256914be79bcf2349b2b8541d8d2a66946
d1984aa87d4372eb00d07731962665bf543c18f9a0c0e615bfe2d4f3ee14a9a09870095d
8a37beffd50b879c71e47ee8f2dcddfbdfd00df57eeff51d96cf8dd5a018a1097bc6d302
dee47f6a0ace0f7cb3106af698538593e2a6d21b2260d7571ab783c
pkE: 0400f46e86f205ee3d04fb3108a4f010186e4699b2795724a7d1f4b99c9c26d8201
6f49b76ea9de34adf3e52acb75fa4e3019b08a4659d16a748ef5c02378b228672b201448
132139c548f3a99bc154a8fc6f8e07b706507b9ad749c8bf2f19c2a9d554267dbfbb967f
1237f3d2adb69480c7b9b87e8206cff14c2296fc5e98d77b091dbcf
enc: 0400f46e86f205ee3d04fb3108a4f010186e4699b2795724a7d1f4b99c9c26d8201
6f49b76ea9de34adf3e52acb75fa4e3019b08a4659d16a748ef5c02378b228672b201448
132139c548f3a99bc154a8fc6f8e07b706507b9ad749c8bf2f19c2a9d554267dbfbb967f
1237f3d2adb69480c7b9b87e8206cff14c2296fc5e98d77b091dbcf
zz: 00c593407d3db9a1f50276c17c08ba1e3fa961a93a5579b86aa790c603dc2ef991cf
22bb48706565133a7e2b7e81faf41a3aee6082927c2cdb55d45f7b162fafcd8101247438
3901917e7aec53257672b4b925ea28c7f934c39bf7fb3a82f1680616392fad013226f263
e8199ac82471e7a91dc19266824a943144780c35ed8bb3423e51
context: 030003000200020400f46e86f205ee3d04fb3108a4f010186e4699b2795724a
7d1f4b99c9c26d82016f49b76ea9de34adf3e52acb75fa4e3019b08a4659d16a748ef5c0
2378b228672b201448132139c548f3a99bc154a8fc6f8e07b706507b9ad749c8bf2f19c2
a9d554267dbfbb967f1237f3d2adb69480c7b9b87e8206cff14c2296fc5e98d77b091dbc
f04012c3c8145099336bc8c2839c5f2a846f38864b2d00d82a7d508e939affa0b9947801
25498a76ec7c9956784e00c249f0811794750722561e571f32879689d878830017943ffa
e1d4b71bfe0bc211ef13e0cee99cd83518ab1fbfb5c26fcb7339810033304458b92aeb56
fa5c4f3808023c0ea872e5bb1d8299f9ae68187c0667278bfce0401a762534eac8a21420
a6801d050a3d256914be79bcf2349b2b8541d8d2a66946d1984aa87d4372eb00d0773196
2665bf543c18f9a0c0e615bfe2d4f3ee14a9a09870095d8a37beffd50b879c71e47ee8f2
dcddfbdfd00df57eeff51d96cf8dd5a018a1097bc6d302dee47f6a0ace0f7cb3106af698
538593e2a6d21b2260d7571ab783cf19e7afbe93b9d8b9837fe0a40ada462caf9a031824
8f66dd7832fac65a58dcacbf170937f825b35d22fd19125483b1f2f6993549423617d8ab
9f65322d627b6490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: 07242daa2387978d3e1c1229dc57864371da204d5023b54ac59bc3db3228badf
74b2887bf91b69deb783a456a3b812357a6b8b86fcb24ad93edd0b3aefcf8073
key: 06af002a959289eca2d9515948378573ef2584c9de852625c2401294cfa7c450
nonce: d290a07b06dae8728c525519
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d290a07b06dae8728c525519
ciphertext: e63c17a0ed0da44934da38e33624823e9f76db4b497cbfd2223a1f7121db
17a90a6b4f04bda950acaa17c437d8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d290a07b06dae8728c525518
ciphertext: 88669212bda82b30f5349c4f598d0db16c4c92695aeb87ef353daef44c9b
1833818d225dd48c4028c90cf35287

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d290a07b06dae8728c52551b
ciphertext: b071431c4e43464a30d969eb4e8bcc25c8e4e58be37571a850f8974eff45
73f0189e149bf93722b62c5ca215b5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d290a07b06dae8728c52551d
ciphertext: 52090366be93d9c1e2a0caacfb1e469a31967f6bae17bbf13370d931ad62
94ac1ded346ea5347438edf679cd1c

~~~

## DHKEM(P-521), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0140596f2e38947e61f38c9ca16dbbc47ad3714b6d477816a4cef04da350e13d704
f0cb0a78f0413c2538839bc5dff7a3835e35b5258146a82b7e93742dc62776a2b
skS: 01c458add2bef29c38dda144a94ede66a541594eff77b4d55e61456a9cfc14423d0
2960a63204047e5ca6025bc7fa4500c86570353cc733a04852d9475a3fed01d05
skE: 00513a119d5f88a77a9e1cb815feb8c43cebe53236388532e0e2808dd3cf00a13a5
01985d205975d0c2c53de1673d2aaa4bb82b48436014955ebe862f58887c8379c
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040112eff836b7463855b866ec557c61f0a2e368a413d7e8bff7f514cd63649fd04
9525ccad508e1bfe4e827d823648a51f9225c19c2ac9de438ad4db65218da4de88b01f9e
3038179d7f1f88d2c235ddf2de3fee105e626c8b8f8c878023e9135d1c7cab41c4d94c20
098d5f5b768ab601ec8c2187b2032d197eef95cb6256c4ec8c8e825
pkS: 04018b664eec503b9ecba3dcc1f53ea5559cd3c49a0fa35be06bd00bdabd1149408
605da7bd897d3ff0cb3104507debc4a72b091598b9d35f42accd635370b1e6ad4f7002a2
a8d1d0bcb70f5687a208496dc9f801ba9aff5cb0466d0304b4b30ccc65da80310f0daeb8
2cdb6c14237fdd0e9926cfcf19945da0f1be434a79acb7a61394cec
pkE: 0400e88d015410dcc541ce3f020dddbf980873d5bc2cb7602a4cd6816265ddaa25e
6135382534b430f697a08612d3663c51b4dd408b2ab7a5b65adf3e35ee77945eb830070c
3bb63e439f35db4cfbbe819219ce082351a6d3e24e641ef0f6c3ed69f3557590f3e4f283
f96e905d73857b9255d2104b42918334033761c5886084ea407eb78
enc: 0400e88d015410dcc541ce3f020dddbf980873d5bc2cb7602a4cd6816265ddaa25e
6135382534b430f697a08612d3663c51b4dd408b2ab7a5b65adf3e35ee77945eb830070c
3bb63e439f35db4cfbbe819219ce082351a6d3e24e641ef0f6c3ed69f3557590f3e4f283
f96e905d73857b9255d2104b42918334033761c5886084ea407eb78
zz: 015a1d050e2cd755d4cff871d8d9694658f3ade6c06bb1d82290308a22dc108f674e
bc94bca1a7f8fdba228fb3967b3fb7a6c0537b986967b709574e85e08d5a7174
context: 000003000200020400e88d015410dcc541ce3f020dddbf980873d5bc2cb7602
a4cd6816265ddaa25e6135382534b430f697a08612d3663c51b4dd408b2ab7a5b65adf3e
35ee77945eb830070c3bb63e439f35db4cfbbe819219ce082351a6d3e24e641ef0f6c3ed
69f3557590f3e4f283f96e905d73857b9255d2104b42918334033761c5886084ea407eb7
8040112eff836b7463855b866ec557c61f0a2e368a413d7e8bff7f514cd63649fd049525
ccad508e1bfe4e827d823648a51f9225c19c2ac9de438ad4db65218da4de88b01f9e3038
179d7f1f88d2c235ddf2de3fee105e626c8b8f8c878023e9135d1c7cab41c4d94c20098d
5f5b768ab601ec8c2187b2032d197eef95cb6256c4ec8c8e825000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000cf83e1357eefb8bdf1542850d66d8007d620e4050b5
715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a53
8327af927da3e490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: 073c9264c804cff8315a034a72c088ef2f9a4e2ad1c0172c5b4b84514248c1a4
c188af37a5e4cbcc9e5338f94e47d2d81e2a82c4ded8e517ac1856c9c10d648d
key: dc948b5131cd6ecd7b2c78e1b888e7c833dd05810bc5a54da2e44aa171374412
nonce: 186c3c23a941aead11588678
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 186c3c23a941aead11588678
ciphertext: a542b40509b53be955470c573ae232da377f72f5d9e8f8b9dbb23b55acec
d390b593d9f9a415b79f1b9e517d8a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 186c3c23a941aead11588679
ciphertext: ec93620950224a7c8278863c132741e9d69082a6dcef5b7fb21e92b0831b
099813a18001a937e1207880bf3fd9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 186c3c23a941aead1158867a
ciphertext: 5a3e0d8d6bd3d3a00075b4a1ba15a23c1b3f540d6a92d7113378a7cc0194
18cc0b0907791a12f882942a673dff

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 186c3c23a941aead1158867c
ciphertext: 2d905643d85d8b742c9e4ad4a4fee6f60eec5b81d257f52c608381c45431
02037bf421500131be9fb171c5eb21

~~~

## DHKEM(P-521), HKDF-SHA512, AES-GCM-256

### PSK Setup Information
~~~
mode: 1
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00e57b0d1d12df7e723057495e90d08e522d09de2c00fb38393e9bdc344e37dd8c0
f2d08fc43360ff946dd58805829748c8866081f61c0077d73ba162f9aec7ce47b
skS: 0054832dd5dd0fe980a3e0022172fe743e7eb40780a985482ca03b182f08b4c974a
db73eecf0ad2ec51b71a5df04b7ce17043d714fae31f48f9cecd3705fa626207c
skE: 0098080ae3db3185d3df3cc3405a729aa5f5e6034fce5c2e53e46a903525042704b
af7d3ea36f4448d9dfec17e65680d168d34fdabed1227317255c76f3a8643e709
psk: 6d656c6c6f6e
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0400ddc139c60056852eef014eff61f75cadf36b07c9d9c3cb37e5bf81a7f64e4d3
d66ce63a0b4808f39e391e209b734179a7d9f4ec7b3e5132cec230adaff1d122f7e015e5
4b99aedf23c1a21b91a08bbb662ca4ad6cd7f3314e584f1fbd0127ba8386e154080399f4
17e8f31741e1ac386ea243e2d0997943bd24ac23f26c0c45c06f2b9
pkS: 0401a63312195bfe66e8165287a4273ea402b6bddb73229ce328e5ed2ec43cc1d2d
73f72e8abbb437c8e1df84702b598205865f6fcb0474bab155f3153de8a6fc28f610139d
b9e4f772b2a9a955d3ab7fc1c45aac3c0f2ca84f4c38e692ee8d186a687f223d5e9dcc8c
ce038f168f2df097f336e2fd71a501743d72c3cd7f2aac73898267c
pkE: 0400c9c705d29ad7bfe8009267205ef37f289a989981c390b7b3bf71948cb072f9d
001995c69f67b0f329df43450ce10cb0e571ea2fb2a3fcefc456ad393302f61da2200eff
79fedbbdf2ad07c6023b8fbf5ed88688b961b2417f8ed5c004f11b10e80165482a426902
3061c211eaa4c51569fb0522871fc3483442548dfb68797da7b74f0
enc: 0400c9c705d29ad7bfe8009267205ef37f289a989981c390b7b3bf71948cb072f9d
001995c69f67b0f329df43450ce10cb0e571ea2fb2a3fcefc456ad393302f61da2200eff
79fedbbdf2ad07c6023b8fbf5ed88688b961b2417f8ed5c004f11b10e80165482a426902
3061c211eaa4c51569fb0522871fc3483442548dfb68797da7b74f0
zz: 00fd027969da1545d7be56bc8b358f55efdb156699c5039068f1e3398a7365515a60
6fe940b7860a4ca31b1ada4f3547f849d76740a793580be0c60c2ef1aa925bb5
context: 010003000200020400c9c705d29ad7bfe8009267205ef37f289a989981c390b
7b3bf71948cb072f9d001995c69f67b0f329df43450ce10cb0e571ea2fb2a3fcefc456ad
393302f61da2200eff79fedbbdf2ad07c6023b8fbf5ed88688b961b2417f8ed5c004f11b
10e80165482a4269023061c211eaa4c51569fb0522871fc3483442548dfb68797da7b74f
00400ddc139c60056852eef014eff61f75cadf36b07c9d9c3cb37e5bf81a7f64e4d3d66c
e63a0b4808f39e391e209b734179a7d9f4ec7b3e5132cec230adaff1d122f7e015e54b99
aedf23c1a21b91a08bbb662ca4ad6cd7f3314e584f1fbd0127ba8386e154080399f417e8
f31741e1ac386ea243e2d0997943bd24ac23f26c0c45c06f2b9000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000f19e7afbe93b9d8b9837fe0a40ada462caf9a031824
8f66dd7832fac65a58dcacbf170937f825b35d22fd19125483b1f2f6993549423617d8ab
9f65322d627b6490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: 74e0856e841f503e6d5c5582addcdbc8fb24c8a30f4ad3c42aa8b278e0167c95
c6cceb734e401c49abb46526af0ea6da47149785e1ccffa749677d95ef29211a
key: 998626ea6cb80083a69d180735559e3e9ed3127e3d308b69291b88535258a517
nonce: 11e1a3d6f2f03f10f2a07b81
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 11e1a3d6f2f03f10f2a07b81
ciphertext: b3a4dfa7abdf075984104894c64caa983a6fd69c1b9447de032589f33c97
bd85bbb90082725b428dad0c909240

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 11e1a3d6f2f03f10f2a07b80
ciphertext: 1b49b6b147c37647d41f20a23775de312ceea21220254c194d1b71608b52
0b313cce074473a1c6384110dff6c7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 11e1a3d6f2f03f10f2a07b83
ciphertext: 8bc2c2f02974041fc464097195362a0ac46872f4a4b8c1f7361c8141f7b2
76699be8cbc84867ab2a813457ea03

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 11e1a3d6f2f03f10f2a07b85
ciphertext: 3d77439937c48fa3ad2ef38d49110f6338d74179a6a9281f0da82022802e
7443aa3e594f8db7a88708753b6a2a

~~~
