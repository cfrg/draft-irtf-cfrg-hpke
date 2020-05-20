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
 -  ins: C. A. Wood
    name: Christopher A. Wood
    org: Cloudflare
    email: caw@heapingbits.net

informative:
  CS01:
    title: Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack
    target: https://eprint.iacr.org/2001/108
    date: 2001
    authors:
      -
        ins: Ronald Cramer
      -
        ins: Victor Shoup

  GAP:
    title: The Gap-Problems - a New Class of Problems for the Security of Cryptographic Schemes
    target: https://link.springer.com/content/pdf/10.1007/3-540-44586-2_8.pdf
    date: 2001
    authors:
      -
        ins: Tatsuaki Okamoto
      -
        ins: David Pointcheval
    seriesinfo:
      ISBN: 978-3-540-44586-9

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

  HPKEAnalysis:
    title: An Analysis of Hybrid Public Key Encryption
    target: https://eprint.iacr.org/2020/243.pdf
    date: 2020
    authors:
      -
        ins: Benjamin Lipp
        org: INRIA Paris

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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/a1335d2eecf6918e7c85de5b4972d5e02c52f3a1/test-vectors.json
    date: 2020

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar3

  NISTCurves: DOI.10.6028/NIST.FIPS.186-4

  GCM: DOI.10.6028/NIST.SP.800-38D

  fiveG:
    title: Security architecture and procedures for 5G System
    target: https://portal.3gpp.org/desktopmodules/Specifications/SpecificationDetails.aspx?specificationId=3169
    date: 2019

  HMAC:
    title: To Hash or Not to Hash Again? (In)differentiability Results for H^2 and HMAC
    target: https://eprint.iacr.org/2013/382
    date: 2013
    authors:
      -
        ins: Y. Dodis
        org: Department of Computer Science, New York University
      -
        ins: Thomas Ristenpart
        org: Department of Computer Sciences, University of Wisconsin–Madison
      -
        ins: John Steinberger
        org: Institute of Theoretical Computer Science, Tsinghua University
      -
        ins: Stefano Tessaro
        org: CSAIL, Massachusetts Institute of Technology

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
implemented and formally verified. It is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions
about the underlying primitives {{HPKEAnalysis}}. A summary of this
analysis is in {{sec-properties}}.

# Requirements Notation

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP14 {{!RFC2119}} {{!RFC8174}}  when, and only when, they appear in
all capitals, as shown here.

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- Sender (S): Entity which sends an encrypted message.
- Recipient (R): Entity which receives an encrypted message.
- Ephemeral (E): A fresh random value meant for one-time use.
- `(skX, pkX)`: A KEM key pair used in role X; `skX` is the private
  key and `pkX` is the public key.
- `pk(skX)`: The public key corresponding to private key `skX`.
- `encode_big_endian(x, n)`: An byte string encoding the integer
  value `x` as an n-byte big-endian value.
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`.
- `zero(n)`: An all-zero byte string of length `n` bytes. `zero(4) =
  0x00000000` and `zero(0)` is the empty byte string.
- `random(n)`: A psuedorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - DeriveKeyPair(ikm): Derive a key pair (sk, pk) from input keying material
  - Marshal(pk): Produce a fixed-length byte string encoding the
    public key `pk`
  - Unmarshal(enc): Parse a fixed-length byte string to recover a
    public key
  - Encap(pk): Generate an ephemeral, fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to pk
  - Decap(enc, sk): Use the private key `sk` to recover the ephemeral
    symmetric key (the KEM shared secret) from its encapsulated representation `enc`
  - AuthEncap(pkR, skS) (optional): Same as Encap(), but the outputs
    encode an assurance that the KEM shared secret key is known only
    to the holder of the private key `skS`
  - AuthDecap(skR, pkS) (optional): Same as Decap(), but the holder
    of the private key `skR` is assured that the KEM shared secret
    key is known only to the holder of the private key corresponding
    to `pkS`
  - Nzz: The length in bytes of a KEM shared secret produced by this KEM
  - Nenc: The length in bytes of an encapsulated key produced by this KEM
  - Npk: The length in bytes of an encoded public key for this KEM
  - Nsk: The length in bytes of an encoded private key for this KEM

* A Key Derivation Function (KDF):
  - Extract(salt, IKM): Extract a pseudorandom key of fixed length `Nh` bytes
    from input keying material `IKM` and an optional byte string
    `salt`
  - Expand(PRK, info, L): Expand a pseudorandom key `PRK` using
    optional string `info` into `L` bytes of output keying material
  - Nh: The output size of the Extract function in bytes

* An AEAD encryption algorithm {{!RFC5116}}:
  - Seal(key, nonce, aad, pt): Encrypt and authenticate plaintext
    `pt` with associated data `aad` using secret key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`
  - Open(key, nonce, aad, ct): Decrypt ciphertext `ct` using
    associated data `aad` with secret key `key` and nonce `nonce`,
    returning plaintext message `pt` or the error value `OpenError`
  - Nk: The length in bytes of a key for this algorithm
  - Nn: The length in bytes of a nonce for this algorithm

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in {{ciphersuites}}.  Algorithm identifier
values are two bytes long.

The following two functions are defined for a KDF to facilitate domain
separation of calls as well as context binding:

~~~
def LabeledExtract(salt, label, IKM):
  labeledIKM = concat("RFCXXXX ", label, IKM)
  return Extract(salt, labeledIKM)

def LabeledExpand(PRK, label, info, L):
  labeledInfo = concat(encode_big_endian(L, 2),
                        "RFCXXXX ", label, info)
  return Expand(PRK, labeledInfo, L)
~~~
\[\[RFC editor: please change "RFCXXXX" to the correct number before publication.]]

## DH-Based KEM

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- DeriveKeyPair(ikm): Derive a key pair (sk, pk) from a byte sequence of
  length Nsk.
- DH(sk, pk): Perform a non-interactive DH exchange using the
  private key sk and public key pk to produce a Diffie-Hellman
  shared secret of length Ndh
- Marshal(pk): Produce a byte string of length Npk
  encoding the public key `pk`
- Unmarshal(enc): Parse a byte string of length Npk to recover a
  public key
- Ndh: The length in bytes of a Diffie-Hellman shared secret produced
  by the DH function of this KEM.
- Nsk: The length in bytes of a Diffie-Hellman private key

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF:

~~~
def ExtractAndExpand(dh, kemContext):
  prk = LabeledExtract(zero(0), "dh", dh)
  return LabeledExpand(prk, "prk", kemContext, Nzz)

def Encap(pkR):
  skE, pkE = DeriveKeyPair(random(Nsk))
  dh = DH(skE, pkR)
  enc = Marshal(pkE)

  pkRm = Marshal(pkR)
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def Decap(enc, skR):
  pkE = Unmarshal(enc)
  dh = DH(skR, pkE)

  pkRm = Marshal(pk(skR))
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz

def AuthEncap(pkR, skS):
  skE, pkE = DeriveKeyPair(random(Nsk))
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Marshal(pkE)

  pkRm = Marshal(pkR)
  pkSm = Marshal(pk(skS))
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = Unmarshal(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Marshal(pk(skR))
  pkSm = Marshal(pkS)
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz
~~~

The KDF used in DHKEM can be equal to or different from the KDF used
in the remainder of HPKE, depending on the chosen variant.
Implementations MUST make sure to use the constants (Nh) and function
calls (LabeledExtract, LabeledExpand) of the appropriate KDF when
implementing DHKEM. See {{kdf-choice}} for a comment on the choice of
a KDF for the remainder of HPKE, and {{domain-separation}} for the
rationale of the labels.

For the variants of DHKEM defined in this document, the size Ndh of the
Diffie-Hellman shared secret is equal to Npk, and the size Nzz of the
KEM shared secret is equal to the output length of the hash function
underlying the KDF.

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

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
possession of a KEM private key.  The following one-byte values
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

* `zz` - A KEM shared secret generated for this transaction
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared secret held by both the sender
  and the recipient (optional; default value `zero(Nh)`).
* `pskID` - An identifier for the PSK (optional; default value `zero(0)`)
* `pkSm` - The sender's encoded public key (optional; default
  value `zero(Npk)`)

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

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
AEAD `aead_id` 2-byte code points, are assumed implicit from the
implementation and not passed as parameters.

~~~~~
default_pkSm = zero(Npk)
default_psk = zero(Nh)
default_pskID = zero(0)

def VerifyPSKInputs(mode, psk, pskID):
  got_psk = (psk != default_psk)
  if got_psk != (pskID != default_pskID):
    raise Exception("Inconsistent PSK inputs")

  if got_psk and (mode in [mode_base, mode_auth]):
    raise Exception("PSK input provided when not needed")
  if not got_psk and (mode in [mode_psk, mode_auth_psk]):
    raise Exception("Missing required PSK input")

def KeySchedule(mode, zz, info, psk, pskID):
  VerifyPSKInputs(mode, psk, pskID)

  ciphersuite = concat(encode_big_endian(kem_id, 2),
                       encode_big_endian(kdf_id, 2),
                       encode_big_endian(aead_id, 2))
  pskID_hash = LabeledExtract(zero(Nh), "pskID_hash", pskID)
  info_hash = LabeledExtract(zero(Nh), "info", info)
  context = concat(ciphersuite, mode, pskID_hash, info_hash)

  psk_hash = LabeledExtract(zero(Nh), "psk_hash", psk)

  secret = LabeledExtract(psk_hash, "zz", zz)
  key = LabeledExpand(secret, "key", context, Nk)
  nonce = LabeledExpand(secret, "nonce", context, Nn)
  exporter_secret = LabeledExpand(secret, "exp", context, Nh)

  return Context(key, nonce, exporter_secret)
~~~~~

Note that the context construction in the KeySchedule procedure is
equivalent to serializing a structure of the following form in the
TLS presentation syntax:

~~~~~
struct {
    uint16 kem_id;
    uint16 kdf_id;
    uint16 aead_id;
    uint8 mode;
    opaque pskID_hash[Nh];
    opaque info_hash[Nh];
} HPKEContext;
~~~~~

### Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
for the holder of a given KEM private key.  The `SetupBaseS()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The KEM shared secret is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

~~~~~
def SetupBaseS(pkR, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, zz, info, default_psk, default_pskID)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, zz, info, default_psk, default_pskID)
~~~~~

### Authentication using a Pre-Shared Key {#mode-psk}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given pre-shared key
(PSK).  We assume that both parties have been provisioned with both
the PSK value `psk` and another byte string `pskID` that is used to
identify which PSK should be used.

The primary differences from the base case are:

* The PSK is used as the `salt` input to the KDF (instead of 0)
* The PSK ID is added to the context string used as the `info` input
  to the KDF

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

~~~~~
def SetupPSKS(pkR, info, psk, pskID):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_psk, zz, info, psk, pskID)

def SetupPSKR(enc, skR, info, psk, pskID):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, zz, info, psk, pskID)
~~~~~

### Authentication using an Asymmetric Key {#mode-auth}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkS)` produces the correct KEM shared secret
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
  return enc, KeySchedule(mode_auth, zz, info, default_psk, default_pskID)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, zz, info, default_psk, default_pskID)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, pskID, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, zz, info, psk, pskID)

def SetupAuthPSKR(enc, skR, info, psk, pskID, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, zz, info, psk, pskID)
~~~~~

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

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
  encSeq = encode_big_endian(seq, Nn)
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
input a context string `exporter_context` and desired length `L` (in bytes), and produces
a secret derived from the internal exporter secret using the corresponding KDF Expand
function.

~~~~~
def Context.Export(exporter_context, L):
  return LabeledExpand(self.exporter_secret, "sec", exporter_context, L)
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

| Value  | KEM                            | Nzz  | Nenc | Npk | Nsk | Reference                    |
|:-------|:-------------------------------|:-----|:-----|:----|:----|:-----------------------------|
| 0x0000 | (reserved)                     | N/A  | N/A  | N/A | N/A | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)      | 32   | 65   | 65  | 32  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)      | 48   | 97   | 97  | 48  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)      | 64   | 133  | 133 | 66  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(Curve25519, HKDF-SHA256) | 32   | 32   | 32  | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(Curve448, HKDF-SHA512)   | 64   | 56   | 56  | 56  | {{?RFC7748}}, {{?RFC5869}}   |

### Marshal/Unmarshal

For the NIST curves P-256, P-384 and P-521, the Marshal function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}. The Unmarshal function performs the
uncompressed Octet-String-to-Elliptic-Curve-Point conversion.

For the CFRG curves Curve25519 and Curve448, the Marshal and Unmarshal functions
are the identity function, since these curves already use fixed-length byte
strings for public keys.

### DeriveKeyPair

For the NIST curves P-256, P-384 and P-521, the DeriveKeyPair function of the
KEM performs rejection sampling over field elements:

~~~
def DeriveKeyPair(ikm):
  prk = LabeledExtract(zero(0), "keypair", ikm)
  sk = "invalid"
  counter = 1
  while sk == "invalid":
    label = concat("candidate ", encode_big_endian(counter, 1))
    bytes = Expand(prk, label, Nsk)
    bytes[Nsk-1] = bytes[Nsk-1] & bitmask
    sk = Octet-String-to-Field-Element(bytes)
    counter = counter + 1
  return (sk, pk(sk))
~~~

where `Octet-String-to-Field-Element` is as defined in {{SECG}}, Section 2.3.6,
and bitmask is defined to be 0xFF for P-256 and P-384, and 0x01 for P-521.

For the CFRG curves Curve25519 and Curve448, the DeriveKeyPair function is the
identity function, since these curves already use fixed-length byte strings for
private keys.

### Validation of Inputs and Outputs

The following public keys are subject to validation if the curve
requires public key validation: the sender MUST validate the recipient's
public key `pkR`; the recipient MUST validate the ephemeral public key
`pkE`; in authenticated modes, the recipient MUST validate the sender's
static public key `pkS`.

For the NIST curves P-256, P-384 and P-521, senders and recipients
MUST perform full public-key validation on all public key inputs as
defined in {{keyagreement}}, which includes validating that a public
key is on the curve.
Additionally, one of the following checks MUST be ensured: the scalar
given as input to DH is in the interval [1, n-1] where n is the prime
order of the subgroup; the result of DH is not the point at infinity.

For the CFRG curves Curve25519 and Curve448, validation of public keys
is not required. Senders and recipients MUST check whether the Diffie-Hellman shared
secret is the all-zero value and abort if so, as described in
{{?RFC7748}}.

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

# Security Considerations {#sec-considerations}

## Security Properties {#sec-properties}

HPKE has several security goals, depending on the mode of operation,
against active and adaptive attackers that can compromise partial
secrets of senders and recipients. The desired security goals are
detailed below:

- Message secrecy: Privacy of the sender's messages, i.e., IND-CCA2
security
- Export key secrecy: Indistinguishability of each export
secret from a uniformly random bitstring of equal length
- Sender authentication: Proof of sender origin for Auth and AuthPSK
modes

It is shown in {{CS01}} that a hybrid scheme of essentially the same
form described here is IND-CCA2-secure as long as the the underlying KEM
and AEAD schemes are IND-CCA2-secure.  The main difference between the
scheme proposed there and the scheme in this document (both named HPKE)
is that we interpose some KDF calls between the KEM and
the AEAD.  So further analysis is needed on two fronts, first to verify
that the additional KDF calls do not cause the IND-CCA2 property to
fail, and second to verify the two additional properties noted above.

This work has been done for the case where the KEM is DHKEM, the AEAD is
any IND-CCA2 scheme, and the DH group and KDF satisfy the following
conditions:

- DH group: The gap Diffie-Hellman (GDH) problem is hard {{GAP}}.
- Extract and Expand (in DHKEM): Extract is indifferentiable from a
  random oracle. Expand is a pseudorandom function, wherein the first
  argument is the key.
- Extract and Expand (elsewhere): Extract is indifferentiable from a
  random oracle. Expand is a pseudorandom function, wherein the first
  argument is the key.

In particular, the KDFs and DH groups defined in this document (see
{{kdf-ids}} and {{kem-ids}}) satisfy these properties.

The analysis in {{HPKEAnalysis}} demonstrates that under these
constraints, HPKE continues to provide IND-CCA2 security, and provides
the additional properties noted above.  The analysis considers two
variants of HPKE usage: single-shot message encryption and secret key
export. In the single-shot variant, S uses the single-shot API to use
the key once to encrypt a plaintext. The export variant is the same as
single-shot variant, except that the sender additionally exports two
independent secrets using the secret export interface. We distinguish
these two variants because the single-shot API does not lend itself to
use the Export interface.

The table below summarizes the main results from {{HPKEAnalysis}}. N/A
means that a property does not apply for the given mode, whereas X means
the given mode satisfies the property.

| Variant              | Message Sec. | Export Sec. | Sender Auth. |
|:---------------------|:------------:|:-----------:|:------------:|
| Base, single-shot    | X            | N/A         | N/A          |
| PSK, single-shot     | X            | N/A         | X            |
| Auth, single-shot    | X            | N/A         | X            |
| AuthPSK, single-shot | X            | N/A         | X            |
| Base, export         | X            | X           | N/A          |
| PSK, export          | X            | X           | X            |
| Auth, export         | X            | X           | X            |
| AuthPSK, export      | X            | X           | X            |

If non-DH-based KEM schemes are to be used with HPKE, further analysis
will be necessary to prove their security.  The results from {{CS01}}
provide some indication that any IND-CCA2 KEM will suffice here, but are
not conclusive given the difference in schemes.

In addition, both {{CS01}} and {{HPKEAnalysis}} are premised on classical
security models and assumptions, and do not consider attackers capable of quantum
computation. A full proof of post-quantum security would need to take this
difference into account, in addition to simply using a post-quantum KEM.

## Security Requirements on a KEM used within HPKE

A KEM used within HPKE MUST ensure the following to avoid identity
mis-binding issues: The KEM shared secret computed by Encap and Decap MUST
depend explicitly on the KEM public key pkR and the KEM ciphertext enc.
The KEM shared secret returned by AuthEncap and AuthDecap MUST explicitly
depend on the KEM public keys pkR and pkS and the KEM ciphertext enc.
This is usually implemented by including these values explicitly into
the context of the key derivation function used to compute the KEM shared
secret. This is also how DHKEM meets the requirement.

## Security Requirements on a KDF {#kdf-choice}

The choice of the KDF for the remainder of HPKE should be made based on
the security level provided by the KEM and, if applicable, by the PSK.
The KDF SHOULD have at least have the security level of the KEM and
SHOULD at least have the security level provided by the PSK.

HPKE's KeySchedule uses LabeledExtract to convert an arbitrary-length
PSK into a fixed-length PSK. This is necessary because of the
restrictions on the key in HMAC's indifferentiability theorem {{HMAC}}.
A future instantiation of HPKE MAY omit this line if: Extract is not
instantiated by HKDF-Extract and there is an indifferentiability theorem
for Extract without restriction on the key's length.

## Pre-Shared Key Recommendations {#security-psk}

In the PSK and AuthPSK modes, the PSK SHOULD be of length Nh bytes or
longer, and SHOULD have Nh bytes of entropy or more. Using a PSK shorter
than Nh bytes is permitted. A PSK that is longer than Nh bytes or that
has more than Nh bytes of entropy, respectively, does not increase the
security level of HPKE, because the extraction step involving the PSK
only outputs Nh bytes.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see {{?RFC5869}}. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret zz
and has access to an oracle that allows to distinguish between a good
and a wrong PSK, it can perform a dictionary attack on the PSK. This
oracle can be the decryption operation on a captured HPKE ciphertext or
any other recipient behavior which is observably different when using a
wrong PSK. The adversary knows the KEM shared secret zz if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

## Domain Separation {#domain-separation}

HPKE allows combining a DHKEM variant DHKEM(Group, KDF') and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to Extract and Expand inside DHKEM and the remainder of HPKE have
different prefix-free encodings for the second parameter. This is
achieved by the different prefix-free label parameters in the calls to
LabeledExtract and LabeledExpand. This serves to separate the input
domains of all Extract and Expand invocations. It also justifies modeling
them as independent functions even if instantiated by the same KDF.

Future KEM instantiations MUST ensure that all internal invocations of
Extract and Expand can be modeled as functions independent from the
invocations of Extract and Expand in the remainder of HPKE. One way to
ensure this is by using an equal or similar prefixing scheme with
an identifier different from "RFCXXXX ". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's Extract or Expand, such as Hash and HMAC in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's KeySchedule this is avoided by using Extract instead of
Hash on the arbitrary-length inputs `info`, `pskID`, and `psk`.

The string literal "RFCXXXX" used in LabeledExtract and LabeledExpand
ensures that any secrets derived in HPKE are bound to the scheme's name,
even when possibly derived from the same Diffie-Hellman or KEM shared
secret as in another scheme.

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
* Nzz: The length in bytes of a KEM shared secret produced by the algorithm
* Nenc: The length in bytes of an encapsulated key produced by the algorithm
* Npk: The length in bytes of an encoded public key for the algorithm
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kem-ids}}

## KDF Identifiers

The "HPKE KDF Identifiers" registry lists identifiers for key derivation
functions defined for use with HPKE.  These are two-byte values, so the maximum
possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KDF: The name of the algorithm
* Nh: The output size of the Extract function in bytes
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
Note that the plaintext is the same for each test vector. Only the nonce
and AAD values differ.

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: a1914f62acf14fa1886ab37a00c348319399e4273d5a09540643065856c09807
skE: 66aa73f67e5e00185ac85328bdb8df58dc2f647845442350df4bbb84e9c8ffcb
pkR: 6cff23d8b2133f50f336e027b2f4fb0bbd050acb3d4edacb1eb7573aa0578d06
pkE: 786212f5b86bff040fb0faf778f17100b228686d68da739340e0d5a954e47575
enc: 786212f5b86bff040fb0faf778f17100b228686d68da739340e0d5a954e47575
zz: 3dcd1bcf2a8f3aff985e8c36a0dad609630a7c4e324e3c3bc1cdbf7c162708ac
context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: ec37110d1043eec728b1c11f5ff2b40240118011781399b923fc6fd736e758a6
key: 8378a695336f0ea767472621a13e4beb
nonce: 323cce16cdef227689b96eff
exporterSecret:
cc330538b6d2cf65e9ecacc11947342eeeceadd8d500e4efe6f7f8ad2ef119af
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 323cce16cdef227689b96eff
ciphertext: e58d8182309bb31a93cc2dd414d034b76a79e6d5445ea2a35b832b958a95
d40783ea8addc63d1da1e66d3b54af

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 323cce16cdef227689b96efe
ciphertext: 6e4c3c62b0fa6aff203cb6670ec12fcd6e6f96ccf0e7baaadb933275275c
9b9855d4bac1bfe503ae070fb41510

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 323cce16cdef227689b96efd
ciphertext: bcb93cb3d5038b540fe7861c628ef41a51ef2a099589b86018d463d25c2d
21d7295be28b24fb24300cab816ae6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 323cce16cdef227689b96efb
ciphertext: e97fa410ee8c4ebd9b15c511566c71ffc78716da0bc7b13d876e2f305425
e909b003e0caddc84c1e304e053ed1

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: b46b650364f4fea30a1b46aea54b10a42e473fd94b921c9bc5240181967f734c
skE: 48b63ae117c1731831c21769c3672b689e5132f47817ea0b619bc3b36c2c0098
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: bc4ed3cf3f988a7c27d54a9bba38827bdea0478310aaa50def0e57d2cf0b6b22
pkE: eb77cedd1100c831df0d8d09cbaaafddcb2358ef179a82c7063fd7eb6a321715
enc: eb77cedd1100c831df0d8d09cbaaafddcb2358ef179a82c7063fd7eb6a321715
zz: d3c7bf2d5c1f83173a7c7bfab969da98a9e7f00ccd8e0731b8c11f0aa4aecf3a
context: 00200001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: b02b07c24ed6a658884fdd4d0f8905c7bd2819a6ab698ff681c3ba794fe86cee
key: 7dbb519b6cebbc342eae64a190612d58
nonce: 971f3da8f6c9b77d9800e5dd
exporterSecret:
ff7f71f64e8c45fdbb04975fc0759e54c77112ef3f627f41f8c80632eb51135e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 971f3da8f6c9b77d9800e5dd
ciphertext: 6048ddc4d9e26b79db832245b5d297a31573d13014d71fd252d11a98e65b
3f30887c5f8632ab67e0d7e79c47d7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 971f3da8f6c9b77d9800e5dc
ciphertext: 4160f296e4569c9ab7ad89575221db790a2f5c7c6be2791427fc06768985
f93912408f55e2e8315af16f4cd4b4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 971f3da8f6c9b77d9800e5df
ciphertext: f199c17d5a522d72cfca6c15858658b22bfc364b13551f90b9fe4ebd8a52
ce43f50608ab9eef4fc28b51c023a3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 971f3da8f6c9b77d9800e5d9
ciphertext: 477984d1c9569c97fbbcbc84ca9fe34fd45dcc365459c593aa4a802025ab
87cd1615358c8b1016f01626039d79

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 1138a341046fc9c2adc10c5e8e448f3721686036953f02ff4d621caed0e967ed
skS: fda85adcf7bb76427763d65e18bf53aa36bd89167fc6161aeaf50bb33ac12cd1
skE: aebe6b066b8d608376bb940255eadec98660e9913b6f16dac17ab13ecba37666
pkR: 9bfd8482c8d588233558cbe38f604561b2b6a9c1cfc6dc5ab48e9c55ecb79a21
pkS: 2856582674ca565993d0291e7a5c02a5369e2b0ad96aa6229bc81261624b8663
pkE: d607fa71d2691bb7748163e0956511c0ee250d6e893a9f982ed50d3d86f58866
enc: d607fa71d2691bb7748163e0956511c0ee250d6e893a9f982ed50d3d86f58866
zz: 76e30cfe0cf6060aa1ea38e26a2c1d73551a316ba5c94cd5595d3c1d02afe804
context: 002000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 31698d5043a36529f6d575450b713e7ea87d81b952b26cf348a686fa54345fa0
key: 6c20d03788e57ddc6b3ed4865c027b90
nonce: 907a7ef5171079c19e7a0f1c
exporterSecret:
8d6d2c07822d7aa4238496cacd2c28c0d911d9d3391da40f0c4392b5e0163694
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 907a7ef5171079c19e7a0f1c
ciphertext: b86b8cdb48d286b18e73b6bc0aa682625df24402ce65462bc55c7af57717
3e3b7ea183b597fd024850c7aed2a3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 907a7ef5171079c19e7a0f1d
ciphertext: 16f86e975a6e197582848fe86fcbf42d55d2dc52033d455605a25ca6a1b0
fc18bead8531462ecd10ca6efa70a8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 907a7ef5171079c19e7a0f1e
ciphertext: 5c6d9263de675951500e779fda1be94de9d5ed9a1ca1f7a54f8c67a5ffb0
ddad56de7840bfdacd675c8d41470d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 907a7ef5171079c19e7a0f18
ciphertext: 6598b7b7997768f1f8964a826e9210d6d232648fc9cc1659002157bb2f4e
adaed9d7c9ad2dd1b739f7ed28021b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: a1760137a00f780d82f114c24d5708798a89cf9089c1d3fb39e969936e52a7c7
skS: 52d635d2af84695e2957c494bcd2a14025e06237cfbef4b1a3d2c8cec4ede60b
skE: 8b79a91d3da9cce3d5f451779da12d6695d4f2e4fed284d5bcfd08422dd7361c
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 13df56ac2717186975ce7cc01bde8e527c1fd091ef1cdc3398668c4b86c91104
pkS: abbb4fc61ee08009f0a32853161f91f79b160424c7761ebbc59ad3591fb0051d
pkE: e6ca611abb7276c51d25c24f1d78ce366241adc2c74f771c59a2e29c729c0f1e
enc: e6ca611abb7276c51d25c24f1d78ce366241adc2c74f771c59a2e29c729c0f1e
zz: 32772bd81a399e9958a7be7fc752994403ed0faacd0614b0325773c998f81036
context: 00200001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: ee4ccc8acc60e62fd42ec053330b59e7d02fa8667f0ab33947e88b4ca8b55366
key: 103ba10b6ddc8a152c8185958c19e573
nonce: 26a17010f9e3def3ed75cc90
exporterSecret:
54353bfbddd1fc5cd8f1bbee0eed46fce999dd27ac0f3087113b39228ea6ec00
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 26a17010f9e3def3ed75cc90
ciphertext: 196ee7ddf37c3bf39b026331b98f8e363e4551f77a97e4e60e88d55c269a
95660a0eecac7ea9c91a7ef1aa4e47

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 26a17010f9e3def3ed75cc91
ciphertext: 05fd5e524c8c2b5769ff7e5af38a5381b63aacf3e9f5dfaba0edcb7ec7bd
4ba4b35ba31197a6ff57aec3f46760

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 26a17010f9e3def3ed75cc92
ciphertext: b4e53661ad2282df502475d6e6150b2dd73e4667f296a6bf4cd364473f36
eb787fe50097467c2fd45eef370794

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 26a17010f9e3def3ed75cc94
ciphertext: 49242dd29249c8d0e527df1d2e132954fe3ba3690ccc34b4179ae3e89329
be8f60aac8c422ac69c26bcfdde062

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d8d9b1323aa07273bb85917949b3c3090ee285c4e153a5d945abdf0a39c6d16b
skE: f7ed61104b0bbb577ce9e84aad9942739a24c3eb711ddcf2f6d33a2be24f1862
pkR: dd96920750f1dcbe002ff8e40d992e1cf103fa071424c22af3f19556235afd33
pkE: 0e58461d88c6d35f48b6fb1f71235ab99b0e81081a69be52b880802cd185a700
enc: 0e58461d88c6d35f48b6fb1f71235ab99b0e81081a69be52b880802cd185a700
zz: f6b5c84990e9c4cbc50e9635fd5e76536a10a451b2eaf6fdf7f46a4d49a93e69
context: 002000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: fcf0615a25fb996fc721383e007790e7c00fce4c38a11f1962d60141a717cf1d
key: e544b216c63cd6edabe3e94131b46907e582bac9b6eec045bedb9ba76aa6851c
nonce: 8993dfcaeae64477b0a4f26b
exporterSecret:
7fa6043485282eb8ef549ff3ebe139781fc2f4b842f8a4462d3b1daac6b985af
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8993dfcaeae64477b0a4f26b
ciphertext: e7ffa98dc23983829698007cc28d3e78bc92a56d5c669cc97d40bba03420
68253e448caa748a818bffa8c37118

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8993dfcaeae64477b0a4f26a
ciphertext: 906da58093113509d497ae430154d5bb0bc5e2234d7f49e8564fdd910f6b
d7abb6bd3d886570b0b0aa3f1f4724

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8993dfcaeae64477b0a4f269
ciphertext: 0ce22d8bdc3ccabdb1a98701812af589b5bc521a2e33b440847699ec3d0a
a1f23aed4afc47cf1883867efb9214

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8993dfcaeae64477b0a4f26f
ciphertext: c0fe1d2e3904a96fa770a40ee630739b72ddddfad617dbc18719dc31f2c3
68284c2b34c575613651d0b9864940

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3b95c1a28430d5becbfcbd734f3b67ad670916aa9a5dd218ce91e000acea14bb
skE: 4b5c6c54f3aaf2ca90d91e648f66869f1272bdf5f23862dc6385c0641b791c8e
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: b6cd3d17f79ccd3ba343e3d01aad4ec344634a493022b01cf18a618262cd092b
pkE: 26b04d75d6569474ae524369c13fc44cb596874d3c7cae5dadc891b6a1fb6530
enc: 26b04d75d6569474ae524369c13fc44cb596874d3c7cae5dadc891b6a1fb6530
zz: d440fa1748643ee71c275d0fcf8fee835650fa9edb56e05ac2ca3e5f9b49b51c
context: 00200001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: aa3a81b5afefa623c244ef3143b4631ca9803870456f3cd3101a76635f355493
key: f58645691367bae3b434e593f1aca7306b17f28694bdcf7e696cf29f83ca0fdd
nonce: d1db6e372466ddaab7b5a145
exporterSecret:
4b9d471c006735850b7495f485a143fd3418441408258abe952048b342c4fc34
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d1db6e372466ddaab7b5a145
ciphertext: d9eceec0d7f8ac725431db9d311929dec0cc322e84ec9d3aebb63c051682
13cf7857552c59d8e8fe4a6d870647

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d1db6e372466ddaab7b5a144
ciphertext: 9621db0a712501caf22c55618b47df7aafd946fdabeb1f6e496a4b4c8347
bb5d3e6466c7884d853cdf8afb19db

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d1db6e372466ddaab7b5a147
ciphertext: 24a127c4e8448338c6af6ba4612d0a1b5e4f836958b3fd6838fae2dba49e
9f72476d6212fd80a86d08d1a315e0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d1db6e372466ddaab7b5a141
ciphertext: a0bbc29f7bc1fb626a7d766ed63ca79eb11ff743f589c91be9e8fd708f27
c0f3ffdf46ba3710e2f3d5f9930dc7

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2d8dc8fe7d777f7aa216911f25e0c70e38822d561bb52712394ea59dd47a1147
skS: 47104ac08ded144be2508eb328b528c057767661e2eacb8eda91c4010e5adaeb
skE: 1fc15f90b4ebfe0ac43709a1013a81dac67f2f2b9f2b53f542150fd832d92996
pkR: 82c248c9586f23e563eedf6d8250679206c6163c9d2092d4046dd5213d21b915
pkS: 7efbb420f56438e5d5fa5ee95fe3f6573033c89d567d045bab6f146958d9b038
pkE: e75e8e60cac307a05f0dd61ae3dc289dff42c715eaddac3e3d0f0b0994470670
enc: e75e8e60cac307a05f0dd61ae3dc289dff42c715eaddac3e3d0f0b0994470670
zz: e1e1f363d1526412ff4dda4891a137565f29f614df71278aaafd4d0e808b0435
context: 002000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 9e163836f429e3652da268910b8d0274bb863cf9ff79d9d1fe9644f3eee17731
key: 7ec6a99fef339adae95010edc011e3178e5d22b1ca63138866cf93d83c2e20b5
nonce: 9d7b8450dce5910cc314d265
exporterSecret:
40896a75c52be5507702575468f2db1c0d3ee5f6294d15a0c3ced341749847cf
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9d7b8450dce5910cc314d265
ciphertext: 6c856e1bb04e5043205a43b01045fe00a177040400d41044042298b013f7
fae4fa859f8d2fd68f9cb14b5f226d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9d7b8450dce5910cc314d264
ciphertext: 7bdd2cbc05ba6c378d1db039616fbfce2b27fd28eb001035c935adb20ff1
dfcd893215a0fa44f9faa9e8e39811

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9d7b8450dce5910cc314d267
ciphertext: d6f1d39d990d81faa217e180991e1985c0afb21c617a7d94560bfbcd7e76
c9d8eb05dcede7ae0a5436e63c7d52

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9d7b8450dce5910cc314d261
ciphertext: 1351ea15f8d63fd2e3e14886e499ffebcd4ec094b6ea6f7e39f77d93ef14
b31d86f3cf0879391e2e604d8487cc

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: b6021b73397e7fa08170398c55d45f925cfef0d4152ffbc26f8f6b42f5db124d
skS: 5b5e37adad3c22030e28d99e5ee216c1ebd1ea9165585841c4241d1709c8b64b
skE: eafab6d8256c79bc9b3671c343e6a0e283044ce4d32c9bcb65b62660ba5bece9
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 68bf9860586888b2224e51b19c37d6e9ae33df1db44d96be18868d156cce2f07
pkS: 6aa60e9dae3a136d85b702adeb3949da039fc262c54c9156c151ad7ce987a33f
pkE: 8f6f0fdcfc95ca095d20210b9ce650d9a6e05fba083754c17aa0816b26b8aa4d
enc: 8f6f0fdcfc95ca095d20210b9ce650d9a6e05fba083754c17aa0816b26b8aa4d
zz: 53246be41a5ec1396421a208e985fdadaded1338d7f76eff94df8c1c70532764
context: 00200001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: b1ad99367cece2110e65c31fb9f334976eb420e0748ff46e1153b26034ff0de8
key: da1bebf829baa1971f855710c56c73ab796788e2df7ab781ce56ca132bba1b25
nonce: abf605f47bc211c6cd17963e
exporterSecret:
5f23b13f8056946f70516b5440547a6bcdb898aa3c0301862f4d47a5f39b3385
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: abf605f47bc211c6cd17963e
ciphertext: 840811958acc4166f60abf0671a62c6b5b4f48c5dd939cccf6f735a1fe95
191e923c5d6cfd8a699f88e3ee6f6c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: abf605f47bc211c6cd17963f
ciphertext: aafcee6b5302754ffd6213e093c3052301c129e4e2787e4e505b616feeaf
37290b00cde45b29e7c7def2bd9325

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: abf605f47bc211c6cd17963c
ciphertext: bac3d029915894ff44108d768a7544f1d2e018baa649739025d4fdf3b85e
cc50d64249d091acd959de17fdf00a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: abf605f47bc211c6cd17963a
ciphertext: 1c4a2d0d58b6a64f2474cb581634adb6b42fa4881eca5f7dc896cbd48e17
a1f2cb09ec6834d2bc6590969bfc94

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 73abb05678baaae2305f1da32233980bd8521977c7cea4a09ca423497c7b4985
skE: 0d8fd08881d227d67938fb3d270210430ce41614b8acd7b06fa6a9a6ce3bacb0
pkR: 04ee136d6b48863fdff852223feece11cd24c40163a744a80bd1aadf484a241e9c2
82a4c5643d0cbf8f844d584fe6427ebeb41d3c7b910b2372d576127bc98b0cb
pkE: 04be8eec6e521e5333c55ce066bbca3d3c18d49081ec9c217615bb3845aaa473679
735b348b11ac84972bc67875b4291880171f0a6237e3c527d4e2560aabbe708
enc: 04be8eec6e521e5333c55ce066bbca3d3c18d49081ec9c217615bb3845aaa473679
735b348b11ac84972bc67875b4291880171f0a6237e3c527d4e2560aabbe708
zz: 301fb2df6316f029f42bb7e4f008970e1b9c3eb94e47ac738c565f3a8dca3a3d
context: 001000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 9051f62cf7186263255e907856bc3c411cb0d0dac762dde689adfe5d89e01d8d
key: 00c168c15ef4645422aba4f6a546fefe
nonce: 03ac9aacf1b6e7c71a7ffb44
exporterSecret:
57b9a4d14abf5431b9bc65980eb3760d096cc43cd951458c9c4bdee24c470773
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 03ac9aacf1b6e7c71a7ffb44
ciphertext: 0cfcbcbb5edb20c335c536ba53f44b74e3f5339175c3b1d48fe94d4aafe3
03dcbb02357c854c75fb146887f4ea

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 03ac9aacf1b6e7c71a7ffb45
ciphertext: 6b18cd1c2e0c906bad8442250c8c6e3ac3e2dbed4c2cfedbd0a8d94326f1
bc04b4033c7af36a005e2808925c8a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 03ac9aacf1b6e7c71a7ffb46
ciphertext: fa33c33d0d12d1075bc9c361b654c6f61fa27fb670214987e971d713bf9f
d8394ffb4ba8b9107984c8677c160c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 03ac9aacf1b6e7c71a7ffb40
ciphertext: 25000e1940d8a30cb82f1a4903a9d88d689b4a37aaa72d7feb33d754c8a6
aa888267836fd948509a0b61e80c56

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 77cd0a695b6f63f06a1e10466260363fc245a1543678b7d386376a4157f673e8
skE: 45534e7036cfc1e4bcc3596b58522fd8ddbde7cb2fd97f30985dff9ed248c057
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 044544ead817c3c9b53cd5f87f6d35b7e24ee8976bad049f73b94af0b5301d76a79
7d7ed8801bb8787fdcea25432d482ce3d4aaee505148b7da1405b1ded87d94a
pkE: 04fc92f396e380c463b4f21b2f06dd2e7120497ab3dd7e850018f89994b6d199cff
74b78eec23ebc5cd67df806804326b89ef944fefefdb045cf88ff9452497fb9
enc: 04fc92f396e380c463b4f21b2f06dd2e7120497ab3dd7e850018f89994b6d199cff
74b78eec23ebc5cd67df806804326b89ef944fefefdb045cf88ff9452497fb9
zz: f36889c687bf2b57caedaec106d5b3a8daebf5cd00932efe1bf1415aa5adebe4
context: 00100001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 37dde8e6275e8c031ae0865aff07cd4ebe777104dbd6d88f0993ab661cc87fff
key: 7f15c05554567e48912c6757fe180f0b
nonce: 970766a4715dfd95b0f3312d
exporterSecret:
ee72cac8786dd91e6ce83f97bcbe416cade3fe6f6bf72e7f994c53ec6e3faa35
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 970766a4715dfd95b0f3312d
ciphertext: df317dc58aec59464a3a3a0c115592a3376d3f801c3e26f92876662e0800
d6fd7d1dd9c9c1067962dbb9493722

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 970766a4715dfd95b0f3312c
ciphertext: c0a840053ad88e43d0f7ce060e0a672d642b70d5abe758781f9f005392fa
1e4b21c77127ba53bfad6b57d0dcc1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 970766a4715dfd95b0f3312f
ciphertext: 7832310e91aa6a68ff2aaef1c785669542b940020d2a3ae9edfd15ec8fe9
5e5abf3470b3caa30d10b00f71703c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 970766a4715dfd95b0f33129
ciphertext: e0852c9269fa4bd990764e2fe6d057b88c795033afd4fcc1173b58ee6d04
94305373f73da117ff8697882d1c47

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: e63dd9e71d8460a4b43bd4565345b7f27cb3e134022be10cfe38b0f6c7f7bbfa
skS: 05da2320f5d7b4c7389267cad7a870abbcd7c27f212de1731fb5e7bed81dabe6
skE: 012d7bc6f631ecc887d7584d14c06c528e61c5e9889534dc4bef2066409dd709
pkR: 04994e1472dc068141ccfa1eb2065995c8352b5aff3ca610fd2967c657dc3884ca6
4ef8cb906e7b2b510492a1e8d83745a4f0433167b3e620ace06e2d18a7eb178
pkS: 0467b6474325394a5073e789bfcf6824f9092bc93df5aeaade0eaebe4ed32240ab6
a5f88f488372a8edd39d884c5211ef2514a3584dc20d874b1806540eecb4d3d
pkE: 04309ac21ea599d9270bb95212fcfed1896ed17527366d562a959cfc7a92fde363d
66e75a3db4b2c567882fcafc372ff3ab01aefa09ca375186d618ee3f75a9035
enc: 04309ac21ea599d9270bb95212fcfed1896ed17527366d562a959cfc7a92fde363d
66e75a3db4b2c567882fcafc372ff3ab01aefa09ca375186d618ee3f75a9035
zz: 870a8836616f444de6ea96c09631c7c9232a8b4089100553c3186a2860b917f7
context: 001000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: a7145f4d451f8670783961cf139fc180f628ed28b6be184fcebf9062ae0eca0b
key: 57e644fd34c980e5e8a4e5f7c4490222
nonce: 4bae41ae5879a52ade84f4a8
exporterSecret:
584178395df7a1b19c630acdce5cc6020841eb42b5f5d252a346c7ce166da582
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4bae41ae5879a52ade84f4a8
ciphertext: 5a07aff2b76ef3880e052ec3410231503f0644bc6c96683f157b85707a7e
8831071785993e2dd6f04d317e5996

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4bae41ae5879a52ade84f4a9
ciphertext: 0496ba095f453939cf74075b51add49db758d5d53f5d346b6eb41ecb733d
1128e34793d50d5601337107ad88b8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4bae41ae5879a52ade84f4aa
ciphertext: b001f073ba310f5f863fb42fb49c8f18f28bfe5a0aae1372d2f80615e3ea
bd724ecec6b47fb4057c95e89e6aa6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4bae41ae5879a52ade84f4ac
ciphertext: 7ef5f9a51bebc6f49746e3fc499768d109c87ffe92d74cf903a2c0201d54
a79fac998bdb71468328716898cf89

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 4293af9b9ccbc4cea68e08ce3d72c376d561ce787868c9ddcb0f075e39220cc5
skS: 717864031fada0ddab1098410e1957359d6cc8fc2c849ed4f3c593bb355cd9db
skE: 781b462049423efaf69df9b2528a809b620eb4c6c73b453c06788e707b3bda48
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0433856aedcfed94a01fd6c07df55d256d956f781f671d6d853c20f3638cd3d9dd4
5cff78f8d181efe22d183b81cc6fba96358c13b9b1a50dbaa4a6dc6e2ed1a25
pkS: 0417ed964eab205d2a6e39263be5bca31b38712c1397150bd3716b99100a0ce792f
8c9f9d452d7b15e1301e594fb2fd6a2076133187729ac1da53421846b405d28
pkE: 0451abfd3231c205d7eb8a2a2c6cd2436cbbbe5c55b4f60ae5b93b54d16492b2b94
e20d21bb4774d6f9ca556d05beac8738d5277dcdd7c007aba880f02860b2cac
enc: 0451abfd3231c205d7eb8a2a2c6cd2436cbbbe5c55b4f60ae5b93b54d16492b2b94
e20d21bb4774d6f9ca556d05beac8738d5277dcdd7c007aba880f02860b2cac
zz: ff21f71a6a28d936433cbe6d72c5308f84ab0748261ce312856a15759cc8d61d
context: 00100001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 8bca59efed9c59e83fb2fae2c5d2a0a020e231cd16673516ac6bdf2f1494d5eb
key: 3b69c1619a3e1a789884c006c701342e
nonce: 483c9cd0609faae31dbe7166
exporterSecret:
60cb3443e4541f6bf11ee270c3d6996593fd81c37dcd78a9f0cebc1e8980d889
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 483c9cd0609faae31dbe7166
ciphertext: 240a5a9fa0de31d2f04b0933b36ae36446d04cf57f8b2cdb712d4109660d
9ff2a5b9014bca2e52e17f3b59ef72

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 483c9cd0609faae31dbe7167
ciphertext: ded00355582321d2d7d573e076b76fbc7d2e7e5d2def20d9577a7f52868c
246b7d563d53b956df6ccf54adfbd9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 483c9cd0609faae31dbe7164
ciphertext: e0d415cfc1f31898c1bbb726dc31368c80f989d2b9d923f573fec44fa71a
a4b6c5596f2e486898d24be505290c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 483c9cd0609faae31dbe7162
ciphertext: 06a14914a3984ad091b708263560e7aa3f03f4e8ed2dbd588978b36b4052
f401ab49581089f60f73653aafc5fb

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0d71821d5a90904fc91987f3b73a70955ddf53df1a52bf71f5897af58e66e4cd
skE: 1789fc94868a11ab3e796be46252e8f234bb599c6087cd37157494068e122009
pkR: 048a3e91c372292d955fefac5ac1ca3ff961ea73ced778947d0d7ddcacc99d1176c
aaa89e49dca2cef4fb21a7ab9e42a815fd6298f087ed3b3d5a88fa8dc525ffe
pkE: 04f0637865ed2b6f7459e2394d26c047bb2b09d295bf527a82975bca26885d95ab6
5fd54f4015b021563f52bd50094bc6079bd1a2941dbbe090632974d76b1af59
enc: 04f0637865ed2b6f7459e2394d26c047bb2b09d295bf527a82975bca26885d95ab6
5fd54f4015b021563f52bd50094bc6079bd1a2941dbbe090632974d76b1af59
zz: 4feccd0b1c1480fabb6707a7b572ea75c145d847566f40114afc07cc3ff26ea0
context: 001000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: cfd2f6fe5783c56d0b681e66996d9805e910d669e19f4c05207fc074dd212583
key: fc19f05e408de0b464745003568e4817fd64d102fd191f551f22555f6c4f1455
nonce: 30ae77465cf53e462e981881
exporterSecret:
72d39c9ed728a6c898a928322f9677da2b3bcf8ba9b6d718fadd634c25e76b45
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 30ae77465cf53e462e981881
ciphertext: 172350da352d848aa23ac3014afd93ad2a90f906578cc301bbdd8f4295fd
ece242a65c274b7e5b2993f58db5e4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 30ae77465cf53e462e981880
ciphertext: a845517cb1faba0fe5acbd68c251e2056fac36bae98ff9e086057a68c814
a1f5544f1ffd232d0b5a1ae3aabc33

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 30ae77465cf53e462e981883
ciphertext: 4997e60430678c36e5ec021bf91b141d911285b31e98ebf73a8166a4592d
87ecd5c5c192c6d6090be8af9b18ce

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 30ae77465cf53e462e981885
ciphertext: 567e42ee58f3e4e70d23cee5ac3f141dbd3db511aff10d565f0af753b587
adaa87399fb7b1a9f84fa72fe5a544

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 50226cbff69b39e4706635c14da3db7dd4d8c0bf9219d954850047d81ca439ef
skE: 56a0a0337dbbc5a870f6fd11f5512a024ee3d2824b578133bef82a755f148eb4
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04791159213388a28f1ed7091e90878f15d87dd5cdab6d81af6872dc7d429542828
f304e611402855ebc7db82ed132b9d0fabb9508ba808c14bfd4512f2ba36b0b
pkE: 04a788ad1bf62d201c40db294aa5ea26ff5605c41c19856d125fc3fbb6543ccb8e8
eb9029502a232df948af4f5ad056f29039ebc2279c2151632298b1e7d18593e
enc: 04a788ad1bf62d201c40db294aa5ea26ff5605c41c19856d125fc3fbb6543ccb8e8
eb9029502a232df948af4f5ad056f29039ebc2279c2151632298b1e7d18593e
zz: 6b81319a4734dcbe8f3a2dc324357c329e6c74c891973f90a3cda438dcab6160
context: 00100001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 38dbb195539d9e1af6a49e6a40f8ce5f08265e2c737327a50e67959dbbf1c8c6
key: 5959b970c9571f5516e8e4d46a859090c922520a372725f41fac99b3b1e792e4
nonce: 93bb6445c69f7d4b13455564
exporterSecret:
ac5f6b15df2744dc3470743b3d280ea5470584bc21cff6c8a34fbb850d68d771
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 93bb6445c69f7d4b13455564
ciphertext: 399e338d8dbff1e29d2497565a41d144a4e7f128d6648df3b3805871f384
dfb1745918bcb4b10f091e4024c3d5

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 93bb6445c69f7d4b13455565
ciphertext: 5e08ab03f0861a5b5cd2e718b46ad8a9a13db26c298533710c5755a3258b
8836ee8e0cdb9951ef141d34f3b634

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 93bb6445c69f7d4b13455566
ciphertext: d8dee8ab310bd5cdeabd4924967b1a3f0a0759a509af65fc5bb9d54b56f1
6446fa4dcd588708068f4e190278f1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 93bb6445c69f7d4b13455560
ciphertext: bee00a18effaa1a9b83017654627de03c992311f6ad1cacd59b9fd28b7b3
f6a7227b24bd009b5dee719fcfe394

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 501c460cf1b750aa57e7f5ccae3622d3d239d4bee581bee16b3e11d14945c0fe
skS: 89f723ee5795457b683b121c05b052d0323aa05f3d034bd5302e8402a3fafb05
skE: dad36698731b2dfdc432223f30251633276c89ca8f8b61a914acc3ca4db063bf
pkR: 041cf95316a6848f598bd6bb732586e0540bcd524f599b85777d98cb3556abf5eb6
44fdfd56beedc80e248cc41fb875a5706488a013f49ace45409225d05811a5e
pkS: 04e3b144bc2c1907f752f729928a19dfcd56e70736797cf10bdf49f43395805db84
2a8f047eba3cf8a94f576f1958ec611b2bc9f0d0da9ec1cf967ca7212b5166d
pkE: 04ed9321f4452e224b99f0f668b04c679ef80623ccd93a70c451909d06c982c433d
ff9c7cb57fe705344d806eb0db0b644861d42b77cd69ac2104b8ad0aa95e556
enc: 04ed9321f4452e224b99f0f668b04c679ef80623ccd93a70c451909d06c982c433d
ff9c7cb57fe705344d806eb0db0b644861d42b77cd69ac2104b8ad0aa95e556
zz: 3a2c22071a79f92ffdc911a0507dd595bc2592b2f213bb026360f539366ca445
context: 001000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: c947be1da39c65f04c59942e47a829ca575df67c24801f84bf5191cccb470cac
key: 391a0abf8ab481400350293ff096706904d22c285ccd29d5737e263bc46c0735
nonce: 8109d650fe692365947af9a5
exporterSecret:
8a20e81e5d65026635c9593d45c74e034d21c2d1cb6c02b048d4a7bed7ebea33
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8109d650fe692365947af9a5
ciphertext: 49285fccf433f8eb6f79f8380ff906754713805fd6b989d920d7eac8cfbf
91ef60986441d2c9d5e9633addbd9b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8109d650fe692365947af9a4
ciphertext: 378022cf62010f5131b4b02bd0901f0f4b23d4b52ff6546fdf3357e47404
4958bfa200d856000f8be60678f6e0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8109d650fe692365947af9a7
ciphertext: 8fbc27184d5461db3e5751b39b96b855bbd8dc8883236de8f41bf76fe786
e4c828435300fe5c6ca73bedd4480c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8109d650fe692365947af9a1
ciphertext: b9e406877ffde5a0b17b1f5e722382cb83d58f85b8841f712fc7930bc0cb
3e8a72dd0db03f1819a889da3ae1b2

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 1251b49af0966df9837de5fe7b09a318dca2a21ef3b6336060625551951b94ac
skS: 80b9e38e225e0ad7231511c2dbc95777cdd69af44e0e7433dfb1d8da315baf25
skE: cf299a9a7f7b81b7b000cb91e104792851e7b3fb26e28e45012dbd8779fb42e7
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04cb284f58a049cd2d59003bd0ae2210341e957f7c1d34c797c228e72a443ad8c96
b0918fe40b796fc767b9b0f55d6ebf8308865e3a92bc9dfae6398a8350f904d
pkS: 04dd7fea98af641fef881af766f261127d278f544d22206ef2890adafd5fe3e406e
5dab43fadb4a19dadfda50378f34ea8a7384c211165e3b4e379cf7e6ccfda4a
pkE: 04d9ee928fb711047bfc19dd2f79b7468e10030b5cc7a264dd99899c2b967eff224
380cc52b3be9c337294452184cb618c0e883ec05b97701d736855ad952d014e
enc: 04d9ee928fb711047bfc19dd2f79b7468e10030b5cc7a264dd99899c2b967eff224
380cc52b3be9c337294452184cb618c0e883ec05b97701d736855ad952d014e
zz: 016048db138b9dca75d0cdacbb2ee5f00f8b821f4db8bb6c3550103b0dab89ca
context: 00100001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: fd06c052c5351e186e564ab0072d3e7d7fdde46ae15e54f2ed14ff511ab8c1ec
key: a55e5a91a80c5549ff040b437b838bdf6c18a8ce19bb205048cf9ed07879eff1
nonce: bbc044da7beb1786cdc4684b
exporterSecret:
e8f57673bd0ecdfccab9174140c14b9c2cadac9c89b24ac4d661dd82be12d239
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: bbc044da7beb1786cdc4684b
ciphertext: 876276bbbdf1d9995c4ac042992d731af51d3f6fe694b23bcc8d00b7b593
56c44415f349e95e27b1f210a9706d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: bbc044da7beb1786cdc4684a
ciphertext: 93dabc28f1a6bbe7d9e72fe8549a22feb0d4fb6b05ff9c00b68550f5f543
6fbd548ce8555d95055e5af62e6b98

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: bbc044da7beb1786cdc46849
ciphertext: 6161e3e05b1391558323dcc4b8f3b40aba2801d816fbf1ac1029d35895db
2f27f8e278b1c86991ac06ccc2753d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: bbc044da7beb1786cdc4684f
ciphertext: 19f40f865e4f4f9e1e01769075ea947aabbd2517d9b284bd5a8459a3048d
cf013f6f31adf98d20a3f12c6cf91f

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00945af70b7ccb35aabfa017835b6d85dc6f43dd48b37dffa831cb1ec4e51de2fd6
da4607c52c6081cdfb4e9317810f177aacaf62253a7303f1815b664ea653a449c
skE: 01c429592ebd724dd55d02804e45bea06aabc0e93dd8954e5ffb1ba13413da3793b
6b66975ed45819b85a281c89c7ca1346632a8d408d3d946f9248ff724d3f9a221
pkR: 0400fb85d952b045f83c6d9fa60c61d02c67120e58e288335e052b48e5975919272
a9c6e1d1be32505cce132465cad4d633e7112766c71c2c1cc03d5877045a7672b5a01aa6
8d3c676ac1e8ed1008f44db548b550d98cf685b12234434b732ad78eca6755664e51773b
907e2eb5a9fe2c39f517b904300542ea5f55cc89ea597fe9621c941
pkE: 0401b9d8ae6105723c58d9e34d7707bc017f8d2c4be55140e2ea412ac8bf0b0db07
42a6a484ce24010d2b39787f518cf8411625ab2a601f20efae980cd3bdb8664773801cd8
74224a2cc62f0ad9b6add5b68d340dedd8d22e9121a84b0d77690900dbe35d13248b08d1
81362dc4e8009116396f66c8e5a0985a7b1c38c8d0951e8d4e781ac
enc: 0401b9d8ae6105723c58d9e34d7707bc017f8d2c4be55140e2ea412ac8bf0b0db07
42a6a484ce24010d2b39787f518cf8411625ab2a601f20efae980cd3bdb8664773801cd8
74224a2cc62f0ad9b6add5b68d340dedd8d22e9121a84b0d77690900dbe35d13248b08d1
81362dc4e8009116396f66c8e5a0985a7b1c38c8d0951e8d4e781ac
zz: 153d6ff2235e0cae9fcabfc65d9001bedea690dbf5594a985745c7105e0dc0312322
dfd301dd0bd4b3f688d2bfc54e3b8f13f112a36f6a154c193acca5e6e7aa
context: 001200030002008ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 0e01cb87de90d992960f5c49cb5ac7d5c4b5572bfc9ffe9e1c397e2350bd1d33
18afc805f151a573ec936249685a812f797d2f17377120ea15e5e9282c66134a
key: 4eed68028b2c78ab8cbf005295ad915cb0839beedbe4ffa47f49d5fe7d864306
nonce: f6068c217ddc179e9c61a157
exporterSecret: c4ae57b657b42ab541cce093bca15920bd4fe6d657c150a0de946b36
0456daa69321473f5757fe2eb60e9205bdca9c48dea5fe98a6b9dd4cf0b0f32b39770fcc
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f6068c217ddc179e9c61a157
ciphertext: 645812ce814184b21e35c1e0a7800d1db72cd8fc9a351a8a7bc34ddb5b70
baf42ff0bdd40e54b997bcc9caa425

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f6068c217ddc179e9c61a156
ciphertext: acf4ffd1d715becc44a1e3151347de491ed2909966eac759eb2eea8004af
e21e89a98a51a2787ac41e1be87c85

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f6068c217ddc179e9c61a155
ciphertext: e3fbda2ce8765fe9dac9a1921bcc45f108130812222fe34e387196ab6ada
e6b9175996d68c2ca2ae0ed0699839

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f6068c217ddc179e9c61a153
ciphertext: 29434dcc87094d9dbb48d30f80ca644d15cd9c5179f5098e725f0073f72c
1c63f52856ee7d4d441b7092a1a748

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 001294c2c67ee02cab9bbebcfc05c6fe674fd4863f720e86dcf91e99e6b18d9e7e0
99298aa0330a31b329ab9bc9464c804ae029fa3f7905b14393043ff463336c7bd
skE: 01f33a8a9f37135c9a2f452ef3a363f82c01cecfad2fd6911646a4ec7ff18d95f3e
c5cb6c3c60e5114687907167436a3f4b7d24986f0594623a4e3371fbef7ef8331
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0400d0ed393bfb17ae7ce9c0f082552c96718085dec35bea4ece2841bf51c2d0fa3
71d73af5d0f673afde7a442ccc60be63e1594917a113a64cf44271d3ca514dc33ee0093d
ac1fea026fef21b47c161b649b1f9151ca7d083c1dd2e169226e51b97a6eb749e5ec1ba0
1889c9adcc81040f368e6715859fd372f5b7f8860852e9e670596c7
pkE: 04018d4033489266d856aef4475b11021cd4b32ea6bf8f402b43d4018df8c098a25
cc145f0324673b65ac49d243863fb2729b63b61e9e593aa5e56d315c13522f5164501d06
1a905f4b02814e2dba240dbc88ff228271f605e6312d01e99ffebe1127e41231d74cdf36
95008752aa8f955223aef0cd096f49e1b9907dc0188009b2849ccb3
enc: 04018d4033489266d856aef4475b11021cd4b32ea6bf8f402b43d4018df8c098a25
cc145f0324673b65ac49d243863fb2729b63b61e9e593aa5e56d315c13522f5164501d06
1a905f4b02814e2dba240dbc88ff228271f605e6312d01e99ffebe1127e41231d74cdf36
95008752aa8f955223aef0cd096f49e1b9907dc0188009b2849ccb3
zz: 80fc72a70f5f3b16de9adc52dfdb5fe070b00288888e442cec92bc99b8027e3f55d4
b289128e8eae099007f210dfa0798fa5c96bd4b635a95f154e29bbc1b4ff
context: 0012000300020119d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 1687ea423f725ed6c5bd6bb3f3c23a8329c685036119c5853117bd76c3f7bc7b
389413ba1ccd13adcca69669fed232c97eb6e0da579935d8515b9754d880b0ea
key: b4cc475ff102da83f58dbb4f06b2c7db8ba9a4f51bf9a7788e1200bf78661b68
nonce: b88eb92dafac92b82a6aa0c0
exporterSecret: bfed8e060861f82cf1195da5b21e3e57242fa163ea1959cdd374af68
920da8f7db6b4594d5634fe7c5faa11e119cba0a682b4d3963a434ea4a96f0459a184541
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b88eb92dafac92b82a6aa0c0
ciphertext: 7e2008f7d30971a83b6659d64be069a8bdd0f44e37747ebfd718a2700d4b
406a22289ff4895fee114bc63a0c6d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b88eb92dafac92b82a6aa0c1
ciphertext: 2291b635ffa25669723fc02648f8901e11217d70a442cb92c381ada99b1e
3ae597f48b2e73a6fbcb2edda5db35

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b88eb92dafac92b82a6aa0c2
ciphertext: f0437c180922bc319c2e202d4cbc2c44bcced3f54abc09bdcbc7a323456b
9631e24a38426a58bf9f050ea1a42c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b88eb92dafac92b82a6aa0c4
ciphertext: c4539fc23c8b932eed85968edaedcd831d7180d852445f7ea0f2e97254c1
b4d8cfa20b82c7311a55799148f2fc

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 001c4eaa5ced9c7cbfe558c8145f510aebe5ac864c44b2c9e547130470f948a5cad
eae28c21abe601c925d1b76f9ba1ef76f5524b992371ec0f9528fd7bbbddd2f2b
skS: 00adc0dba6b71660d8b0a825b31ac2634c384140144dce9a6590dde0351c14e2346
7e60c95a902b4ba964597007bb84af2ddf844a693cb89af6842feb0a2c7569377
skE: 003792a1c440f0945003ba509f07a34f8cc71ee351c12b27ee655dd587ea3a69d72
5ba9691ff1f6d1d57cd58c5548134a8c45c7838d1d42b10881e5d2b9c55a973e7
pkR: 0401da5aecc06aaf11b406499b4913eab411e8d1dae484709430fd184d8f11e8cb6
dc3e13a1854c5cd170579dd2cc7092428a2c2a4c34bcb48b8f59bd930fca77c70a30055a
fefc416699eec018906345001bd672acad06784723f5577bba62f803b64e3a78fa7fc99a
91281842b3ac0e430db74a2223ccd103b831fcf4c8f9b79dd487459
pkS: 040082583f7cbe41a6bee792c01a47736e8391efefdff3f43a2cffcdf4fad0cabe6
1c097a734d697b437ba88bfa4d980ecf2c3be21820572ea734a57dc8f38d212e85701245
e8039ceefb84417808250f9672b81d9ec3d541b36488742fef71e389032b42f3c591b1d9
d3e5853e4ffa685e78b82567fd7b492b1d4d6d352ac200ec7c42c11
pkE: 0401f9b7932423e4b17a26e06ead06827b2c3e828a75eea8915691026eec7bc355e
95ed38175d63faa15cc364342b33c303d3c017a8d887a7c00832c516a13d6b0371401bc1
b6011ef260bfb7814ed82c93570b76c5e703406b01134e7773615ba1857fd412dc985ec3
0b22e3630cd8c5acf6dc388e39301d484198bfb28d4a4424f2fc4e7
enc: 0401f9b7932423e4b17a26e06ead06827b2c3e828a75eea8915691026eec7bc355e
95ed38175d63faa15cc364342b33c303d3c017a8d887a7c00832c516a13d6b0371401bc1
b6011ef260bfb7814ed82c93570b76c5e703406b01134e7773615ba1857fd412dc985ec3
0b22e3630cd8c5acf6dc388e39301d484198bfb28d4a4424f2fc4e7
zz: a9726cf488f493182fe82988e4458b7d007e932905b8c2dfad49f9e6ee076f93697f
59e68f412c56a5e7ba024bd81df5c82059697246dacbb21a78f64febfb33
context: 001200030002028ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: a48412a320c0f89a9295115e32f490919ddb74f8a3acb4d87b8d2871901431a2
59d9e86fd1c6538c2c7a816985cceb18abffb9b5bd20a191fe78ff959f4418e0
key: 01decf94dfeb0fbd5dc3b058cc1d85aaae8c5fb652352f67c179a0699d6c550b
nonce: 44a14515052c26bf26ff009a
exporterSecret: c77caa47c8493a962d9282edf2c3d018587ebd1c09cebcbc207794e8
8674b34553548310c9ecc479ec33030a96547a9cfbdfc093901d26ee2a6cfda15f6f1b33
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 44a14515052c26bf26ff009a
ciphertext: f6db27f014e0ac19a4aad7e10ae2fcb6dd56d094eafee01697c655044abe
80234777ee8d13a94cc2c21deccce8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 44a14515052c26bf26ff009b
ciphertext: 148cfa046c2c76744d9c1dd651dcfde10c3fb4b578e0c68befaa6a007a40
6ac141639b5a95fb1dce95a909a90f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 44a14515052c26bf26ff0098
ciphertext: c045834a92dd5eb05f9302ad121965c52a9d581306025eab0247145f7eda
45e33faaed202b7c2a4263e937818b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 44a14515052c26bf26ff009e
ciphertext: c3ebe72802690a0c9a4645e558d54d5c50890c95f2861a5516a26618bf06
0e42f9dcc5db4fed7a64c451724f5f

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01643abccf3d8e5e1b734c819b0af3f92fc19bad0f1d7f4e745ec3bb435d3671148
d07580264c4d950963bc25dc17bf713c19c9bad114ee0e9d54a23df28474b5998
skS: 01c36f377ef65bbe307213107e2c17dee3bb2042f1c77f6c7c60dc14869dedd9cd5
fc1c384840286784f77e2a61c46f7364ecc8a77ae4bafc6e606c73b474a7070ba
skE: 00f41e3792c2c3c61f5676bc939539fb8ee267f6af88906708da15b2e48616a6243
11bc6c842aed59ba7f1005f454403083b629b855b4e6563fdb0d4e98ba51a5d5d
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04017e5075ddf4c8d03427829ff273b87bcaed5091ce6363931df8de358af631804
2dac00dab370ceb1ea94dda0760eb97720dbecbe0e4a67cf11a5fba60300aaa95e40123d
804d56443f84639a25334e3da15de29554b64a40fc2060e537f0144cae127e61ccc62870
b0a2a522e2fb821426edbe0ab9b47eb42d3802292191081a358abf6
pkS: 040078f1f432f32afe90fd0a6d134606e3e219e4f0633c76f656178903b50b35abb
8b4202715f978d79fd18dbf17f9bc5cdb00d1b6ca3f328938d724c2ac5d65b539e000160
3d7e709d103d04126314bdbef9c04d22eef7650e7acc5d0c7d3ae877a1e11500bc3e9979
21b08bf26906f5488ba8f400d35fe6cdd3db26bb485bde054bd0972
pkE: 0400d3a59763631663acb3b7ef4c80341271226081af03963a37221a5d7c5218d7e
5c9aa3553e6f6debdb91301b82565aa2ea1a8879ffdc7db65b1b0eec66ce64768a500314
950da3901bcdaedd6145ae226981170037da82b704a0fa3bbba753fc8635ca47f6645a7a
4b5843e2e3d2e217ad1345e35f363f60e9a7220ed5722a787225d3f
enc: 0400d3a59763631663acb3b7ef4c80341271226081af03963a37221a5d7c5218d7e
5c9aa3553e6f6debdb91301b82565aa2ea1a8879ffdc7db65b1b0eec66ce64768a500314
950da3901bcdaedd6145ae226981170037da82b704a0fa3bbba753fc8635ca47f6645a7a
4b5843e2e3d2e217ad1345e35f363f60e9a7220ed5722a787225d3f
zz: 4a5f577ea82c0d31077eeb3d10f0d59226a3bf798b072f66f3017589d054d57d3741
7bd858c4ca58246da4e065ab23175b7c6db445652c4211e760171310fcdd
context: 0012000300020319d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 5c0aad000f906059cf3f55ce7feaa9d49be19770bf6743dc11c826400641b370
369404d27916d256ea3cd75ed7b78913ff4c736c8d295b659cb2629038a40502
key: 61f47c017357dbe61aeb091b64f6c2ddca2e4a74a9fa7df177e089bf2d7c30c9
nonce: ae4e7aa8562059411daf29a3
exporterSecret: 595db1fede0aabfaea2591b3f8f3d34c379ac6c671abc234b74012f6
4188c339faca9321b2af5dc88b34ceb2c8e6c902861df44feda23efe3767c239709614f6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ae4e7aa8562059411daf29a3
ciphertext: d161d634706ca43e8ab7c1be43793f6d1ba232927f4f552641c04292151f
f6b6aa2801521c2d64d395947f2ea9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ae4e7aa8562059411daf29a2
ciphertext: db10786034a23b52439d39b706025dcf1ca49aff7699ca7fa38c73eb38ec
9df8b7d63427011f5f2e2540104418

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ae4e7aa8562059411daf29a1
ciphertext: 358761f1178edfb278cb8236d395cb336a619735c0c8699bdcea07363861
9f6578c8c4d3c57f94096d61d62b43

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ae4e7aa8562059411daf29a7
ciphertext: 3f3c3e459431de5e2ff7dac940c45aea8615b8b3d36ca2e426a1dc677781
767d58bfead73a55b2804fac6318ef

~~~
