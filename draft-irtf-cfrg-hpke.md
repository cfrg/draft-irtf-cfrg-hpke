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
    authors:
      -
        ins: Victor Shoup
        org: IBM Zurich Research Lab, Saumerstr. 4, 8803 Ruschlikon, Switzerland
  ANSI:
    title: Public Key Cryptography for the Financial Services Industry -- Key Agreement and Key Transport Using Elliptic Curve Cryptography
    year: 2001
    authors:
      -
        ins:
        org: American National Standards Institute
  IEEE:
    title: IEEE 1363a, Standard Specifications for Public Key Cryptography - Amendment 1 -- Additional Techniques
    year: 2004
    authors:
      -
        ins:
        org: Institute of Electrical and Electronics Engineers
  ISO:
    title: ISO/IEC 18033-2, Information Technology - Security Techniques - Encryption Algorithms - Part 2 -- Asymmetric Ciphers
    year: 2006
    authors:
      -
        ins:
        org: International Organization for Standardization / International Electrotechnical Commission

  SECG:
    title: Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2
    target: http://www.secg.org/download/aid-780/sec1-v2.pdf
    year: 2009

  MAEA10:
    title: A Comparison of the Standardized Versions of ECIES
    target: http://sceweb.sce.uhcl.edu/yang/teaching/csci5234WebSecurityFall2011/Chaum-blind-signatures.PDF
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

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar2
  NISTCurves: DOI.10.6028/NIST.FIPS.186-4
  GCM: DOI.10.6028/NIST.SP.800-38D

  fiveG:
    title: Security architecture and procedures for 5G System
    target: https://portal.3gpp.org/desktopmodules/Specifications/SpecificationDetails.aspx?specificationId=3169
    year: 2019

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
such as those based on RSA or ElGamal.  Encrypted messages convey a
single ciphertext and authentication tag alongside a short public
key, which may be further compressed. The key size and computational
complexity of elliptic curve cryptographic primitives for
authenticated encryption therefore make it compelling for a variety
of use cases. This type of public key encryption has many
applications in practice, for example:

* PGP {{?RFC6637}}
* Messaging Layer Security {{?I-D.ietf-mls-protocol}}
* Encrypted Server Name Indication {{?I-D.ietf-tls-esni}}
* Protection of 5G subscriber identities {{fiveG}}

Currently, there are numerous competing and non-interoperable
standards and variants for hybrid encryption, including ANSI X9.63
{{ANSI}}, IEEE 1363a {{IEEE}}, ISO/IEC 18033-2 {{ISO}}, and SECG SEC
1 {{SECG}}.  All of these existing schemes have problems, e.g.,
because they rely on outdated primitives, lack proofs of IND-CCA2
security, or fail to provide test vectors.

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

- Initiator (I): Sender of an encrypted message.
- Responder (R): Receiver of an encrypted message.
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
  - Encap(pk): Generate an ephemeral symmetric key and a
    fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to pk
  - Decap(enc, sk): Use the private key `sk` to recover the ephemeral
    symmetric key from its encapsulated representation `enc`
  - AuthEncap(pkR, skI) (optional): Same as Encap(), but the outputs
    encode an assurance that the ephemeral shared key is known only
    to the holder of the private key `skI`
  - AuthDecap(skR, pkI) (optional): Same as Decap(), but the holder
    of the private key `skR` is assured that the ephemeral shared
    key is known only to the holder of the private key corresponding
    to `pkI`
  - Nenc: The length in octets of an encapsulated key from this KEM
  - Npk: The length in octets of a public key for this KEM

* A Key Derivation Function:
  - Extract(salt, IKM): Extract a pseudorandom key of fixed length
    from input keying material `IKM` and an optional octet string
    `salt`
  - Expand(PRK, info, L): Expand a pseudorandom key `PRK` using
    optional string `info` into `L` bytes of output keying material
  - Nh: The output size of the Extract function

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

def AuthEncap(pkR, skI):
  skE, pkE = GenerateKeyPair()
  zz = concat(DH(skE, pkR), DH(skI, pkR))
  enc = Marshal(pkE)
  return zz, enc

def AuthDecap(enc, skR, pkI):
  pkE = Unmarshal(enc)
  return concat(DH(skR, pkE), DH(skR, pkI))
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
| mode_psk_auth | 0x03  |

All of these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient
2. Use that context to encrypt or decrypt content

A "context" encodes the AEAD algorithm and key in use, and manages
the nonces used so that the same nonce is not used with multiple
plaintexts.

The procedures described in this session are laid out in a
Python-like pseudocode.  The algorithms in use are left implicit.

## Creating an Encryption Context

The variants of HPKE defined in this document share a common
mechanism for translating the protocol inputs into an encryption
context.  The key schedule inputs are as follows:

* `pkR` - The receiver's public key
* `zz` - A shared secret generated via the KEM for this transaction
* `enc` - An encapsulated key produced by the KEM for the receiver
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared secret held by both the initiator
  and the receiver (optional; default value `zero(Nh)`).
* `pskID` - An identifier for the PSK (optional; default
  value `"" = zero(0)`
* `pkI` - The initiator's public key (optional; default
  value `zero(Npk)`)

The `psk` and `pskID` fields MUST appear together or not at all.
That is, if a non-default value is provided for one of them, then
the other MUST be set to a non-default value.

The key and nonce computed by this algorithm have the property that
they are only known to the holder of the receipient private key, and
the party that ran the KEM to generate `zz` and `enc`.  If the `psk`
and `pskID` arguments are provided, then the recipient is assured
that the initiator held the PSK.  If the `pkIm` argument is
provided, then the recipient is assued that the initator held the
corresponding private key (assuming that `zz` and `enc` were
generated using the AuthEncap / AuthDecap methods; see below).

~~~~~
default_pkIm = zero(Npk)
default_psk = zero(Nh)
default_pskId = zero(0)

def VerifyMode(mode, psk, pskID, pkIm):
  got_psk = (psk != default_psk and pskID != default_pskID)
  no_psk = (psk == default_psk and pskID == default_pskID)
  got_pkIm = (pkIm != default_pkIm)
  no_pkIm = (pkIm == default_pkIm)

  if mode == mode_base and (got_psk or got_pkIm):
    raise Exception("Invalid configuration for mode_base")
  if mode == mode_psk and (no_psk or got_pkIm):
    raise Exception("Invalid configuration for mode_psk")
  if mode == mode_auth and (got_psk or no_pkIm):
    raise Exception("Invalid configuration for mode_auth")
  if mode == mode_psk_auth and (no_psk or no_pkIm):
    raise Exception("Invalid configuration for mode_psk_auth")

def EncryptionContext(mode, pkRm, zz, enc, info, psk, pskID, pkIm):
  VerifyMode(mode, psk, pskID, pkI)

  pkRm = Marshal(pkR)
  context = concat(mode, ciphersuite, enc, pkRm, pkIm,
                   len(pskID), pskID, len(info), info)

  secret = Extract(psk, zz)
  key = Expand(secret, concat("hpke key", context), Nk)
  nonce = Expand(secret, concat("hpke nonce", context), Nn)
  return Context(key, nonce)
~~~~~

Note that the context construction in the KeySchedule procedure is
equivalent to serializing a structure of the following form in the
TLS presentation syntax:

~~~~~
struct {
    // Mode and algorithms
    uint8 mode;
    uint16 ciphersuite;

    // Public inputs to this key exchange
    opaque enc[Nenc];
    opaque pkR[Npk];
    opaque pkI[Npk];
    opaque pskID<0..2^16-1>;

    // Application-supplied info
    opaque info<0..2^16-1>;
} HPKEContext;
~~~~~

## Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
for the holder of a given KEM private key.  The `SetupBaseI()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The the shared secret produced by the KEM is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

~~~~~
def SetupBaseI(pkR, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, pkR, zz, enc, info,
                          default_psk, default_pskID, default_pkIm)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, pk(skR), zz, enc, info,
                     default_psk, default_pskID, default_pkIm)
~~~~~

## Authentication using a Pre-Shared Key

This variant extends the base mechansism by allowing the recipient
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
def SetupPSKI(pkR, psk, pskID, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(pkR, zz, enc, info,
                          psk, pskId, default_pkIm)

def SetupPSKR(enc, skR, psk, pskID, info):
  zz = Decap(enc, skR)
  return KeySchedule(pk(skR), zz, enc, info,
                     psk, pskId, default_pkIm)
~~~~~

## Authentication using an Asymmetric Key

This variant extends the base mechansism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkI)` produces the correct shared secret
only if the encapsulated value `enc` was produced by
`AuthEncap(pkR, skI)`, where `skI` is the private key corresponding
to `pkI`.  In other words, only two people could have produced this
secret, so if the recipient is one, then the sender must be the
other.

The primary differences from the base case are:

* The calls to `Encap` and `Decap` are replaced with calls to
  `AuthEncap` and `AuthDecap`.
* The initiator public key is added to the context string

Obviously, this variant can only be used with a KEM that provides
`AuthEncap()` and `AuthDecap()` procuedures.

This mechanism authenticates only the key pair of the initiator, not
any other identity.  If an application wishes to authenticate some
other identity for the sender (e.g., an email address or domain
name), then this identity should be included in the `info` parameter
to avoid unknown key share attacks.

~~~~~
def SetupAuthI(pkR, skI, info):
  zz, enc = AuthEncap(pkR, skI)
  pkIm = Marshal(pk(skI))
  return enc, KeySchedule(pkR, zz, enc, info,
                          default_psk, default_pskID, pkIm)

def SetupAuthR(enc, skR, pkI, info):
  zz = AuthDecap(enc, skR, pkI)
  pkIm = Marshal(pkI)
  return KeySchedule(pk(skR), zz, enc, info,
                     default_psk, default_pskID, pkIm)
~~~~~

## Authentication using both a PSK and an Asymmetric Key

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKI(pkR, psk, pskID, skI, info):
  zz, enc = AuthEncap(pkR, skI)
  pkIm = Marshal(pk(skI))
  return enc, KeySchedule(pkR, zz, enc, info, psk, pskID, pkIm)

def SetupAuthPSKR(enc, skR, psk, pskID, pkI, info):
  zz = AuthDecap(enc, skR, pkI)
  pkIm = Marshal(pkI)
  return KeySchedule(pk(skR), zz, enc, info, psk, pskID, pkIm)
~~~~~

## Encryption and Decryption {#hpke-dem}

HPKE allows multiple encryption operations to be done based on a
given setup transaction.  Since the public-key operations involved
in setup are typically more expensive than symmetric encryption or
decryption, this allows applications to "amortize" the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this decryption must be
stateful.  Each of the setup procedures above produces a context
object that stores the required state:

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

Each encryption or decryption operation increments the sequence
number for the context in use.  A given context SHOULD be used either
only for encryption or only for decryption.

It is up to the application to ensure that encryptions and
decryptions are done in the proper sequence, so that the nonce
values used for encryption and decryption line up.

~~~~~
[[ TODO: Check for overflow, a la TLS ]]
def Context.Nonce(seq):
  encSeq = encode_big_endian(seq, len(self.nonce))
  return xor(self.nonce, encSeq)

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.Nonce(self.seq), aad, pt)
  self.seq += 1
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.Nonce(self.seq), aad, ct)
  if pt == OpenError:
    return OpenError
  self.seq += 1
  return pt
~~~~~

# Single-Shot APIs

In many cases, applications encrypt only a single message to a recipient's public key. 
This section provides templates for HPKE APIs that implement "single-shot" encryption 
and decryption using APIs specified in {{hpke-kem}} and {{hpke-dem}}:

~~~~~
def Seal<MODE>(pkR, info, aad, pt, ...):
  enc, ctx = SetupI<MODE>(pkR, info, ...)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def Open<MODE>(skR, info, enc, aad, ct, ...):
  ctx = SetupR<MODE>(enc, skR, info, ...)
  return ctx.Open(aad, ct)
~~~~~

The `MODE` template parameter is one of Base, PSK, Auth, or AuthPSK. The optional parameters
indicated by "..."" depend on `MODE` and may be empty. SetupBase, for example, has no 
additional parameters. Thus, SealAuthPSK and OpenAuthPSK would be implemented as follows:

~~~
def SealAuthPSK(pkR, info, aad, pt, psk, pskID, skI):
  enc, ctx = SetupAuthPSKI(pkR, psk, pskID, skI, info)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def OpenAuthPSK(skR, info, enc, aad, ct):
  ctx = SetupAuthPSKR(enc, skR, psk, pskID, skI, info)
  return ctx.Open(aad, ct)
~~~

# Algorithm Identifiers {#ciphersuites}

## Key Encapsulation Mechanisms (KEMs)

| Value  | KEM               | Nenc | Npk | Reference      |
|:-------|:------------------|:-----|:----|:---------------|
| 0x0000 | (reserved)        | N/A  | N/A | N/A            |
| 0x0001 | DHKEM(P-256)      | 32   | 32  | {{NISTCurves}} |
| 0x0002 | DHKEM(Curve25519) | 32   | 32  | {{?RFC7748}}   |
| 0x0003 | DHKEM(P-521)      | 65   | 65  | {{NISTCurves}} |
| 0x0004 | DHKEM(Curve448)   | 56   | 56  | {{?RFC7748}}   |

For the NIST curves P-256 and P-521, the Marshal function of the DH
scheme produces the normal (non-compressed) representation of the
public key, according to {{SECG}}.  When these curves are used, the
recipient of an HPKE ciphertext MUST validate that the ephemeral public
key `pkE` is on the curve.  The relevant validation procedures are
defined in {{keyagreement}}

For the CFRG curves Curve25519 and Curve448, the Marshal function is
the identity function, since these curves already use fixed-length
octet strings for public keys.

## Key Derivation Functions (KDFs)

| Value  | KDF         | Nh  | Reference    |
|:-------|:------------|-----|:-------------|
| 0x0000 | (reserved)  | N/A | N/A          |
| 0x0001 | HKDF-SHA256 | 32  | {{?RFC5869}} |
| 0x0002 | HKDF-SHA512 | 64  | {{?RFC5869}} |

## Authentication Encryption with Associated Data (AEAD) Functions

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-GCM-128      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-GCM-256      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |

# Security Considerations

[[ TODO ]]

# IANA Considerations

[[ TODO: Make IANA registries for the above ]]

--- back

# Possible TODOs

The following extensions might be worth specifying:

* Multiple recipients - It might be possible to add some
  simplifications / assurances for the case where the same value is
  being encrypted to multiple recipients.

* Test vectors - Obviously, we can provide decryption test vectors
  in this document.  In order to provide known-answer tests, we
  would have to introduce a non-secure deterministic mode where the
  ephemeral key pair is derived from the inputs.  And to do that
  safely, we would need to augment the decrypt function to detect
  the deterministic mode and fail.

* A reference implementation in hacspec or similar
