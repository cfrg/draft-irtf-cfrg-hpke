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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/d1dbba6a0ff837cf13432e5ec810d232ec5a6062/test-vectors.json
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
  key and `pkX` is the public key
- `pk(skX)`: The public key corresponding to private key `skX`
- `encode_big_endian(x, n)`: An byte string encoding the integer
  value `x` as an n-byte big-endian value
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`
- `zero(n)`: An all-zero byte string of length `n` bytes. `zero(4) =
  0x00000000`
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - GenerateKeyPair(): Generate a key pair (sk, pk)
  - MarshalPk(pk): Produce a fixed-length byte string encoding the
    public key `pk`
  - UnmarshalPk(enc): Parse a fixed-length byte string to recover a
    public key
  - UnmarshalSk(enc): Parse a fixed-length byte string to recover a
    private key. This function can fail on some inputs.
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
  - Nzz: The length in bytes of a shared secret produced by this KEM
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

- GenerateKeyPair(): Generate an ephemeral key pair `(sk, pk)`
  for the DH group in use
- DH(sk, pk): Perform a non-interactive DH exchange using the
  private key sk and public key pk to produce a Diffie-Hellman
  shared secret of length Ndh
- MarshalPk(pk): Produce a byte string of length Npk
  encoding the public key `pk`
- UnmarshalPk(enc): Parse a byte string of length Npk to recover a
  public key
- UnmarshalSk(enc): Parse a byte string of length Nsk to recover a
  private key. This function can fail on some inputs.
- Ndh: The length in bytes of a Diffie-Hellman shared secret produced
  by the DH function of this KEM.

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF:

~~~
def ExtractAndExpand(dh, kemContext):
  prk = LabeledExtract(zero(Nh), "dh", dh)
  return LabeledExpand(prk, "prk", kemContext, Nzz)

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = MarshalPk(pkE)

  pkRm = MarshalPk(pkR)
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def Decap(enc, skR):
  pkE = UnmarshalPk(enc)
  dh = DH(skR, pkE)

  pkRm = MarshalPk(pk(skR))
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = MarshalPk(pkE)

  pkRm = MarshalPk(pkR)
  pkSm = MarshalPk(pk(skS))
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = UnmarshalPk(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = MarshalPk(pk(skR))
  pkSm = MarshalPk(pkS)
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

For the variants of DHKEM defined in this document, Ndh is equal to Npk,
and Nzz is equal to the output length of the hash function underlying the KDF.

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

* `zz` - A shared secret generated via the KEM for this transaction
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

def KeySchedule(mode, zz, info, psk, pskID, pkSm):
  VerifyMode(mode, psk, pskID, pkSm)

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

The shared secret produced by the KEM is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

~~~~~
def SetupBaseS(pkR, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, zz, info,
                          default_psk, default_pskID, default_pkSm)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, zz, info,
                     default_psk, default_pskID, default_pkSm)
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
  return enc, KeySchedule(mode_psk, zz, info, psk, pskID, default_pkSm)

def SetupPSKR(enc, skR, info, psk, pskID):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, zz, info, psk, pskID, default_pkSm)
~~~~~

### Authentication using an Asymmetric Key {#mode-auth}

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
  return enc, KeySchedule(mode_auth, zz, info, default_psk, default_pskID, pkSm)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, zz, info, default_psk, default_pskID, pkSm)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, pskID, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, zz, info, psk, pskID, pkSm)

def SetupAuthPSKR(enc, skR, info, psk, pskID, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, zz, info, psk, pskID, pkSm)
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

### Marshal

For the NIST curves P-256, P-384 and P-521, the MarshalPk function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}.

For the CFRG curves Curve25519 and Curve448, the MarshalPk function is
the identity function, since these curves already use fixed-length
byte strings for public keys.

### Unmarshal

For the NIST curves, P-256, P-384, and P-521, the UnmarshalSk function
performs the Octet-to-Field-Element conversion according to {{SECG}}.

For the CFRG curves Curve25519 and Curve448, the UnmarshalSk function is
the identity function, since these curves already use fixed-length byte
strings for private keys.

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
is not required. Senders and recipients MUST check whether the shared
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
mis-binding issues: The shared secret computed by Encap and Decap MUST
depend explicitly on the KEM public key pkR and the KEM ciphertext enc.
The shared secret returned by AuthEncap and AuthDecap MUST explicitly
depend on the KEM public keys pkR and pkS and the KEM ciphertext enc.
This is usually implemented by including these values explicitly into
the context of the key derivation function used to compute the shared
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
* Nzz: The length in bytes of a shared secret produced by the algorithm
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

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: d3c8ca6516cd4cc75f66210c5a49d05381bfbfc0de090c19432d778ea4599829
skE: b9d453d3ec0dbe59fa4a193bde3e4ea17f80c9b2fa69f2f3e029120303b86885
pkR: 10b2fc2332b75206d2c791c3db1094dfd298b6508138ce98fec2c0c7a4dbc408
pkE: 07da186c37d11e92d924fd1a75aff87d11860dfd59ea940429d8b874de846a33
enc: 07da186c37d11e92d924fd1a75aff87d11860dfd59ea940429d8b874de846a33
zz: 79f0c71200a133c4e608a1d2dab5830e54ba7ee71abd6522cfc4af6ad1c47ac2
context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: e7a85117b9cac58c508eeb153faab0a8205a73d4fca1bb7b81d1a4b504eb71f8
key: ab86480a0094bfe110fca55d98dccafd
nonce: 4a5fc401e6551f69db44d64d
exporterSecret:
eb9570b621c3894a182c40ee67ed9d71bcfb114e2315b2ceaaade6454fa21291
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4a5fc401e6551f69db44d64d
ciphertext: 1ae0fe213b0c230f723d057a9476a5e95e9348699aec1ecfe67bd67a69cb
63894b5aed52332059289c44c4a69e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4a5fc401e6551f69db44d64c
ciphertext: 00e8cec1e413913e942a214fd0d610fdcbe53285491d4e7bbfff51c11b40
1c9e150cac56757e074d923d0de840

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4a5fc401e6551f69db44d64f
ciphertext: 244862294f4036de67304d9f24da1079f4f914c8ffc768999065c657dda4
0c0572c0d04e70d72cf3d150e4bf74

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4a5fc401e6551f69db44d649
ciphertext: 4acf4661c93dc673a6d6372167f2a356c13e430e61a84ebc1919bf26dbc7
d0132c7a54f9698094ddae52ac8e8f

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 1f68f688b24c27f825012d40efa4fb33e033d717d569047a702c3ef5a64bde64
skE: 8ad4455d6eda442a9731ac224c9f8a468f489c77e3871cde9ebdd12e9027bad7
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 6f61735fee57c59ce6489d80a11d77b7b2f9e9fddc3cb0bff0cf5a982ce7f344
pkE: 97adf1e077a6ae6f98e3eb4bf09743eb989a8e2d1c6013009b6629f701e70b75
enc: 97adf1e077a6ae6f98e3eb4bf09743eb989a8e2d1c6013009b6629f701e70b75
zz: d81e257a13d4081e0a91f68ecba8d517ca907a9061f463bf11b5f7b200f60a3f
context: 00200001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: c8fe7dd0ddc92d4d0fafb8b5c44ef049a94d12d0952472fc8b3f153d89a5585b
key: b5a7f8235cd2513056fce3b58df2eabe
nonce: bdc674179679e243d134faab
exporterSecret:
d71ee6abf3b3439203946824aa302ea6f7099cdee02f1b6c29c3165809d15c03
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: bdc674179679e243d134faab
ciphertext: eb4fc6ffed9fca50793bbddc9754805d219ec8a987ceb4838e644e12a8c1
a86b69a44cb3353399471008b9ea47

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: bdc674179679e243d134faaa
ciphertext: de242daa1d77832292c81e5a8c9b8f534a5de656437af16ebb497b0c6382
8d80d37f7043e95b24acd44a0489ac

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: bdc674179679e243d134faa9
ciphertext: d2ad57dc8006b4b451a470a96babc5e85e6690f2a4a28566a3b393962dc6
8ba2907d91f9705aa007d58dfc0195

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: bdc674179679e243d134faaf
ciphertext: 2d9f83c5c40e73d32e60438bf216dc9e87bc45518a175cbf9cd47d10417a
beeac1e5ba9ff5db1c9e4d14861bcc

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 41ee53399ebae982cd067fefa138b6b401cea1a7ef428fe9d6bc90e903a88f6e
skS: 55799581f14ec785dbaa11857700adf78f842a51b5ae6a4b4e5a4d99c66e5793
skE: 367299c0da446bfa8f3b41382c58b1b77fdadb5cf056d1fe94d6ab0b8741a184
pkR: 777b10479021ffb3d21ff7ad0d7ff1a27220f6203e729826a71dc1dd7f77ed27
pkS: 2bba172f178cf852e8670e574fdcdd62d8dcfa063548d3424d84f3e403f4e64c
pkE: b6c5c1515f6aebcde4e78ed492672489d1cb7c9256935dd1514eede9ee956a59
enc: b6c5c1515f6aebcde4e78ed492672489d1cb7c9256935dd1514eede9ee956a59
zz: 806664f6a174c0f72a64ec3e671a9c584388c2dd40f5b0eec4def8e69d549b7a
context: 002000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: e4ceff245d1e1781b54191a2f4520ccc8523d59244c975309975e69afe61b896
key: df3a747864781866dac633f56b101cd9
nonce: 94ef1cb07771719d1bf62d15
exporterSecret:
3f6b2cbca577b5842d57dffd6be0be512afa19adb16f09085c57014032c87609
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 94ef1cb07771719d1bf62d15
ciphertext: 483a276f138d5b33f2d32c4345c109078fc203716e2f9f16ffa991510cc4
f60df8583fc0133cb1ddad93b1a6b9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 94ef1cb07771719d1bf62d14
ciphertext: 347263ce760a935e3d1d85fb30377b54c6c77ed5d29458cdef341071be78
29424d3901b061ad36090bcb9d1338

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 94ef1cb07771719d1bf62d17
ciphertext: 7a4dd7aa889668797f264c73b5a675400bbea5437589e85a2fcd3595a211
d7cd09399fa70b3907e1a4198aaa8f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 94ef1cb07771719d1bf62d11
ciphertext: 0b24f93f5f3301ad4147a35a2da898a817b5e95623ad849b85cbebf832d3
204657adf1b88201a39b62247a1251

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2fe8ef0b6fdf5f8da2b43472ca05bc324f7e6aabd9e2b65b2dfa5b892f832a20
skS: aede8f90d017a796c2dc73f3674168837a0ca0afaf3577b6aeeb784dc0b31c49
skE: 84a883acd803f41ea16ec23e81ebe3af3cff34fa3c6b50616d67511404d3daa0
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 09171abdb6c6c8833791cb29357e39c2dbd5d6a7c1ed726f77bbdca5eddf397a
pkS: 92bf662e7ae5fda99130c32334f556803b00a419bb726386017c1fe217fb0e3d
pkE: 96fefa84ac1222b735cc60cbd396cfe9303c36d3ac3e46920867b8fef6453e20
enc: 96fefa84ac1222b735cc60cbd396cfe9303c36d3ac3e46920867b8fef6453e20
zz: 0619ce18b92e56d8aa45e21e3db5a4106a7b3f4a640b9c73cd404c33a63c578d
context: 00200001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: d2edc245ee148829587fe394de1a74dd84072169db5fa58bd840c773dfb51e7f
key: a8f14e6db85577e0185343a6842bb2da
nonce: 4e77fea157276c67eee96eb4
exporterSecret:
9e9eb41a697cea5dc9b56cb3ac052cfb0c0ab4ca79125bb9a2add7df99d17680
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4e77fea157276c67eee96eb4
ciphertext: 07d4728a9d239425e493cbdbff32d317f76823e4b0b4c12d8128a79b776b
61f7d01bcaf6d07bc1265225766553

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4e77fea157276c67eee96eb5
ciphertext: f820deea546cdc9f911aa6a6834ebfccf9775ff64997f5a8f704eed9dc6e
90b88b9a935b58c574fbe3a449ed91

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4e77fea157276c67eee96eb6
ciphertext: ec0873cfac98eaa3ada7a9c9d69831fb530cb140f427b991585336fd3579
7c01367c53e3a154682e58c1f75338

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4e77fea157276c67eee96eb0
ciphertext: 4392ee0bf464ee58565e6e48b2b92444ec913b2a7e72520352008f1b0405
d8eb17c2a2f25715bc9bb216794b72

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0a2737d281922bdd223db035c4c0b4154179f338e20dd45b3cb6e801bc078229
skE: 43f15e4141a3532e03d5b974ab4dae83c8e3b460ab0ecdfb5b38451ef35ade1f
pkR: cd965e8af97e58598b02ebaef2d376e430a7a744fe64b58ac37c0ad8a026dc02
pkE: 0298cbf0d065c0c4d5fad9367fdae4350d2ca07b66936c70f9d8a61a64271707
enc: 0298cbf0d065c0c4d5fad9367fdae4350d2ca07b66936c70f9d8a61a64271707
zz: fd311e3b861d9ce5ddb89a37bd5b76f5d08f50a10ce4499ffe8aa8934e7222bf
context: 002000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: faf0773568a55c251d1d9590e88f8464fa544271c178f90f4c177e9cfaad152a
key: 954b77e7b3e5db38142f19cda6ace6948e154aa2bc1a193ac90f89565364512c
nonce: f49ff6240b6d611a2bf9af90
exporterSecret:
2e9eb4e338775bc70dd4f5bf1b6f2d0d4565472456cc8b70baa631841e6085e2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f49ff6240b6d611a2bf9af90
ciphertext: 744b9a6332791b799d6f2160697bf2c127df9a0bd35e708ea3d0e165b0f1
180fe9f7a863b7624f14584c6d12c8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f49ff6240b6d611a2bf9af91
ciphertext: 7f95fb427ec720e03f5b9f29b56f9f78c065ac3538469ecdb9672cb2a077
d7d42ff85f9ed7e58bfbf14502b1a1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f49ff6240b6d611a2bf9af92
ciphertext: 143f13b9130768a2f31c418b251cd2320ce0ab25eeb711894f57fa5468ba
ac30a89af146db36506d80ff15f687

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f49ff6240b6d611a2bf9af94
ciphertext: 6231544225e67367b0384da833d4c286ae1cf752ef87eb7511e9c1d3c94c
97df03e0dbebd4d3dd74c753e4bd11

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d9fc87b82f8a33f645dee49ab3945609b670addfa723daa4c56a0c2a84f0e800
skE: d390185c18ec0450f6457e198a41578cd3352c663bc699ee9d05dd94c458b30a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: e0040bc38b3c4f6adf38c8c320ed052ba4978d6d1434bc5c0a9b621565f35b07
pkE: 6e3f42494e8559f9fd4ac7de6968d5f2d5dc9384ed5d2ca1c6fbfaec1df60a26
enc: 6e3f42494e8559f9fd4ac7de6968d5f2d5dc9384ed5d2ca1c6fbfaec1df60a26
zz: 5af485df917bb1ed84f8e81fa052d7a8ea691ef1f79497580f527a13d25303e5
context: 00200001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: fba87fa024ee0f262e6cf3d67fe4906b5b29f22a0dbc88d0935122ef2cc88d1a
key: f2f2678f9f4b374583f489ba96e55bb9f2f8e6e0907fb3f5c5ad195227d3ebf4
nonce: fb7ee240dbc798e289d2257d
exporterSecret:
adb177cf73b15b540274b21c1bca954e2747cf89248fb3bbf6b49bcfe0916afe
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: fb7ee240dbc798e289d2257d
ciphertext: 6195d5f07881a2ce18b0b0bfdd5573570bca3c85ebfe46a90f6c0dfea853
6607556457f46dc5cbfade0860af40

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: fb7ee240dbc798e289d2257c
ciphertext: 5429ab8e9abaf28dc17f8f718ee16597c2ede60eabdfa83465c6400d01bc
3ee602965d97e17de04b8b2e6c5fed

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: fb7ee240dbc798e289d2257f
ciphertext: b38ed602dde69e86f841f86762ca903dc61760c6bc80587a3fbd2c601234
18d446c8c136a6de9e01ff90714c6d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: fb7ee240dbc798e289d22579
ciphertext: 88f59e40b44fd7c8d78846fc6a7bfb1d926217c309b4fbcd1d12a1a4f81a
9147943828dfaf2aa292da1a2557dd

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 877963e68a4566f1b5288dc2a90d43a3378dc91a8b8bd0b82a056cbb5d00da2b
skS: 123e50b6d7b4d867b5d7e7dfea050a5f8a724231f4c510a85eca81a33bcd7f4f
skE: 5cf743372f26b2de271f5ffa859f82f5d0e9c2b67ce27843ce23947eee56062a
pkR: 0cbfc21809b19ac7170fac26b82b782fb93abb2863fc6e98eb3b103a3ff06b08
pkS: 96d4517062bd034b1416e2e34f534a99566b7a2f230af60263bd9949e9062920
pkE: 8330db3fc4c1d027582f11760620404b9f1c54673d95e65d6368b868f008a043
enc: 8330db3fc4c1d027582f11760620404b9f1c54673d95e65d6368b868f008a043
zz: b54fae67eb84a10f0a806ff0f6d2a14f7e1cd0df2999e5dfaddb2c1743c8fd37
context: 002000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 3e1ce250d829206d52269ee6aa0751db9f9e652fe86732347b30ac202a5f7d57
key: 55df035baceee1f8a4978e8f9e7fa9e9874e77ae38fc073a88539d651fbe324c
nonce: 2299e07956f1139c29ada886
exporterSecret:
3679ee6ead22aa73c4100a566ef03054cbd7495985a1d9419a9084c9723d8b47
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2299e07956f1139c29ada886
ciphertext: b6ad165f780d080b3cbaa1631a68bcb34ddbee05287a08f094bfb8c27ecf
9ffb5c3fb8c9f4e900a6e8d4288291

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2299e07956f1139c29ada887
ciphertext: 10973fcd96f1ad80608933dbad1b4eb8fcef67bff6a191c059406d20b2ec
65572d11bd0adae546e395499f8a8e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2299e07956f1139c29ada884
ciphertext: 555ef7aad531a6f408874194751c8c97b314feddf064515b309a650cba7d
1a502c963f566810f784864a718f5b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2299e07956f1139c29ada882
ciphertext: 07acdf32be09d94aef3b46814d993150520534a7e8eb70a238a677e1da27
9cd2911255ad6c740ab3fb0ca7b17b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 8fb4161e1c10167ea42102f183f1c8b7a2b0f78fa3da7608962f1bb912239b48
skS: 8aec40900c4f3cc4b41ff7731794be32586dfb071827798d5f3502324de35804
skE: 34c9a993a628f4f0a31c9426a0614113e37abaebd8dfd8c1cb7fd1f81b2b5ff4
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 42c5a8da45cbf754476ffa53efba8f99228ec7d0ec5a42ad6de0b20a9f0e5100
pkS: 183916ee13bfe81ac65c950b160ce592093b2e82ba986d1b2fa1dc8b85ef0b2a
pkE: adf5d04089b87bf0bbddea2a4afc8b233b2c84d592480e6a42ae37d9047ae861
enc: adf5d04089b87bf0bbddea2a4afc8b233b2c84d592480e6a42ae37d9047ae861
zz: 462c4cb9e3f2e5fe306407a3d83fbab109fbfcb9ae2f0c907872bba316ed218e
context: 00200001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 8c6ddabbb4de438d936cbcffce1d8863807e77ea84c4e2ed89c48008a8f200b2
key: 5a97c5379909006e26e418986461050980730e660c6b742d3ba2c479aea655eb
nonce: 43914a79a085d008b4d57e2b
exporterSecret:
21079400d4f4d2681972da4058bd80101bfb835410dc324ee5b728650f800dd6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 43914a79a085d008b4d57e2b
ciphertext: 6f29d2f8de3391cce245c13d60e824c30a9d312e3763f93aeed26d68d8b5
3f56a52591a58b4058279ce50bae33

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 43914a79a085d008b4d57e2a
ciphertext: 2d8696f79ee6ee4b535b5b2e5a4a92c495c0f7e83a30457328db73a53b11
3671e72a93db707bb758ea00750d90

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 43914a79a085d008b4d57e29
ciphertext: 2ecb5612ea793f10d9f6789adbe1d015d4c4ca41478cd084d42e2b22a5d2
7f54ec139aa63e812f9bab12794fd1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 43914a79a085d008b4d57e2f
ciphertext: 142d3aafbd7204feb783d90ce5cc9cf6b431229b05a8c5e48e672dab4ed7
d8b864a02d22ef9ae4b7d48f64ee0d

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 8ce3034248a152ec76086ce59f96f70b8b30d34223013b91f0c1b72db8f65491
skE: aa40ae4c159a0b05d999dfb58273798f848660c037e8950cd053f85b4331b114
pkR: 04cea2c9b90f4699d30742f6e98e560fe658a6ed44aa6e762f8178284e241627291
44a84be182319f44a97a56a56ef36c5af2f6c6035e2824b7e1c70c87ca73fb8
pkE: 04a475670b8b2caa8ebd061d60841f0fab440ff3e47ffadb57e12d930defdae5458
1411dc5ae829252f39c21aa13a90fc1cdf7cf8267aff2d21bf4bc2344ef7c1a
enc: 04a475670b8b2caa8ebd061d60841f0fab440ff3e47ffadb57e12d930defdae5458
1411dc5ae829252f39c21aa13a90fc1cdf7cf8267aff2d21bf4bc2344ef7c1a
zz: f8ebfc5aa173226b1f74008e96851b888e03e5f200f346dd4ecb3483772714b6
context: 001000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 30c1c027ec32ede4ed3f9cbe008826e6bf9c0774acb1621f0bc992816e6d34c8
key: 6b29fb48d602a77c490730dfd8db1c32
nonce: 347a3181fd00871872150e20
exporterSecret:
2ac910bbcad401f286dfd6b42ce0344dfb30eefe689909e3a0f9e3f50488cb94
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 347a3181fd00871872150e20
ciphertext: 64974c8d8307c15588c4cbc39888abb7daa5debc6eed2942522bb459c177
f1d41c0ba8fb988509502840a1155f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 347a3181fd00871872150e21
ciphertext: 0ae15506a0a749e1bc22709019dcb726f8b6e27879d091e9d30c5cd1600e
37602c11b7fe29a9299a84104603d7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 347a3181fd00871872150e22
ciphertext: 04a7f0097660ff8fb968ac10c5e88bb39b0b24b77b2a0b7b139cc3fface8
82d540d3e874a0cb248fd7b7868b36

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 347a3181fd00871872150e24
ciphertext: fa0cb0114408aafea87145bce7ad80caa73c4f2e75009193700f5f358929
841d7de7af2375bf538b7021e625cf

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 323c91c1fdb3de3c19d2efdcb08383573987a826383bacd7e53e3b47b83009bb
skE: 559f14988c9696cba734cbbe65f5be6ad80936b2b0b09a42637060dd2f2eabcd
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0494def2a8ac76f8b6801c53cde72b8c0dbe4874d09e966154f46523ff1bc6635ea
3ddcbe06e4d714f8d3b56549e699941a9a0752ed307a888a8c6ed9858bdf1f6
pkE: 0442b4481553f81a349b6e6d818bc8b1a98fac95d90fdd5b9c38eb5fa6c43eb1938
0bccb234d6771eac9d6fde6406d210ac2508ea112363fab5c13f940683146f8
enc: 0442b4481553f81a349b6e6d818bc8b1a98fac95d90fdd5b9c38eb5fa6c43eb1938
0bccb234d6771eac9d6fde6406d210ac2508ea112363fab5c13f940683146f8
zz: 4832712586db709f9f7db84349a2ce04efe11aa4f824c34a88963d6d43b94057
context: 00100001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 73922c96909aab9c4f5e9d57e0cbf7d321443a7cf7ead1fdbe38af54317af2e5
key: 61a7dfc6a5eb7a84cd9fc3caadefb9cb
nonce: 2fd7b8ee053eb831e122320c
exporterSecret:
fba725a6e3f9b1d0e2ce6630488613823890d6cbcf0c98aa5494936104200517
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2fd7b8ee053eb831e122320c
ciphertext: 492ab3aa89ba33252bdfdbce4e4f7a23d0695504c488c929c274679f0489
9ad082ed6d86f1b1eb29890752ee6f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2fd7b8ee053eb831e122320d
ciphertext: 970114ed6dd7fb8344869547fc562a20cc1455c4842d37ae1b7b09af7575
56ab7f4e2c83df4ad39cdcca4457ec

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2fd7b8ee053eb831e122320e
ciphertext: f035ba5dd833449db4caeca2551fee2125f7504fdaca2817b2070d05c108
727d2d0c80c0580b05d393728a531e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2fd7b8ee053eb831e1223208
ciphertext: 4c057faac0cb511a983ee755aca841ffb318a0fad7aecf298d4369aac227
1dc2593a534e0307e8708f30841590

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: eef04d3fc02f18a062e08a9f8360543dfb8ebf4e56816bf4187b46d38a2b461b
skS: 6a99366d689f03edb7853ef7becf089ad88fe1ce5f7e7a417ec3f27f4b7e738d
skE: 262a94df44d1c8512a58230d6668c136c44725272a120e36eaac7a66f7a4a651
pkR: 0488b9f57ddc29f4a217105136c840c6885600a7513026bf5f63153c6aeb721c03d
ca83bd1c41fbe3b9f4356c2987b85e4a9804116a6c49f368a7d78a922b0aa1d
pkS: 044cc663be95914919bc00ab7adc0040cfa91fd414d95e181ee8ac3958f267c130a
b1e6381475e0b1db5e0287a1c92b9fe2f3554e45a8aee77b561e01be3648dbc
pkE: 0423485e66ed4b9588897084890edfe6d9231970fa205033d0052f1717df3a38913
e19582e91594a515e3585c4169e13f747eb3d6e3d6fa6e85b444a2e098e204f
enc: 0423485e66ed4b9588897084890edfe6d9231970fa205033d0052f1717df3a38913
e19582e91594a515e3585c4169e13f747eb3d6e3d6fa6e85b444a2e098e204f
zz: 8636eba180c99b1928fb5b26567127d63d32d0adfa1f7498d4fc865d0bbb75de
context: 001000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 8af9fb4c52dc530a9b1ecd6fb03f42fe73033ea92ac25fd9e0121ff107424470
key: a5d872aa51960fb036354655a43f1744
nonce: c1010a9a308a1269e56a34c4
exporterSecret:
8c53501a3e6a156f17b4e5004ba83eedcf20749bb4019d9f2647a984b8b5945f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c1010a9a308a1269e56a34c4
ciphertext: d64fd203f9eaacad9c5d5bfa02b85bcc56ecc647a7e22dfdd41e848c6eb1
7cad015bb3876e04848e3397917cea

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c1010a9a308a1269e56a34c5
ciphertext: e52ad5e01ad414243512e6fb754874c627cffa5636b9410dd7c90215b623
3cbf10baa61eaf2e7916a7df482355

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c1010a9a308a1269e56a34c6
ciphertext: b3bfc4d5ff816be531a9675ea788d62cb24d9c1e8aa1d50396dda0e2d68d
579cb2ab4f349055bb87b8b9859232

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c1010a9a308a1269e56a34c0
ciphertext: eb279949e754e837ab43cbfb1fd926614f834e0e736ffafcfa6202295b72
485506dfa07902e7eb0f16f2f4131c

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: e646ffe3cb25b225f861eefaca510c4ae30ec8cdd553c92e256f99964050db01
skS: d318c373e5695f682a12f05b8665f86ca826437e6999dcf65c4a30e57312b884
skE: b23e72f9ed8d928145eca9064a646e04d85053ebf04d0d208aa402ff6dad6d4b
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 044fc24b2c9aeea57d5526c92c80086253466da4c8dfe480df8306d7486738384d2
1e1c0fbfa48a2fd7e8b13df5c5de741ab7fe4b44202d88038c509fdb7f2bb40
pkS: 04b7fdb991a4dfc4c97fdd6d0bff3f58f823022340b065e0851e4efbad47e54e3a4
b8b0a13f7c90d47cd261fc988c1091ecf536979d4aee01949ea1186c28dbc73
pkE: 04694e64c16bb5d570b8ea3488fa38f6f025b765058707bf1784bd23e50bb6fa54f
a7b9cd5727aa3127dd636ac711b67c14cc5e85a899cd6eebe5abe1d0d0fb7b0
enc: 04694e64c16bb5d570b8ea3488fa38f6f025b765058707bf1784bd23e50bb6fa54f
a7b9cd5727aa3127dd636ac711b67c14cc5e85a899cd6eebe5abe1d0d0fb7b0
zz: 9b880502e7179714a0b00328d7d005768561e7f2298e6d52b71d6bee356b6af2
context: 00100001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 689afd96d86da261a3b2c20eb78379e73d867de0dd9754d0992b2d7d2c0904c5
key: 6e8677b2d99afd2a3ea1040f3712cb84
nonce: ef405eb8f9c29f15f7927f36
exporterSecret:
ee804fea20f91550e63129acb7cced2f4f553a20fb31778ccc8ac4e03de7cbf2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ef405eb8f9c29f15f7927f36
ciphertext: f3a737bf395649b497651bd1be77b51ae37ef1ffbcb10e6c91563048546c
f3788c7c9544e91be5668840b9295d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ef405eb8f9c29f15f7927f37
ciphertext: b69a519bf35246d2e1e88a597557bf1603a9e7e433a56413ce03d125159a
021209bb65595ae9e8a9a74edda6de

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ef405eb8f9c29f15f7927f34
ciphertext: 4e4758c5d4f324d5618d19207c14a2abfe9057415cf764d28749bfb1fefd
2e6cadebae943efb3382522a39c05b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ef405eb8f9c29f15f7927f32
ciphertext: fe1ee1416faef36103a5970cd7b4b435381f91de7d09f540c0b8bc1e40c7
a037b143b05f54cfd5dffc26b09e6f

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 92ef45282082dcfeb7fbe45df7b7219a8ad6d04107854da9e0c24c5fec995907
skE: d529d27f3f516374cffa738c32c42911de67b0a8e2d2c57a9944cd9ad83ae3e0
pkR: 04b557e4dc4d085424bf3b7db2d06da3a49d8250e9466bf5a2a386af3ed773c8cd3
e2720a0115f1e0735aa0f8e4921eadf5a6168733126895db328d4aca63774e9
pkE: 04f89bdd9a29e59bfabf6ea6fc890467b19a72eb132fefc25c507528f1de9766009
684970917bb01c3a18111d12989580c78856ccd0558cda541e42b62f165c767
enc: 04f89bdd9a29e59bfabf6ea6fc890467b19a72eb132fefc25c507528f1de9766009
684970917bb01c3a18111d12989580c78856ccd0558cda541e42b62f165c767
zz: 6754f2f2e4bf83c07edae7c3127b118e00262f8606d5af329dfadb93ff2728bf
context: 001000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 3124bd770b176e77a832c8e4090bdab9ca1f1c27bf2e95db875151745433d69f
key: dec7c88f4d0a3716355a9ef8d7cfb99f26d4cc3286fe9589c2de5d83cfd1915f
nonce: f12fab01ef1837996f90e12d
exporterSecret:
34de33c174ce13b57f5e22b6b464b78a69abcef1ca5613e448732289602bbdc8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f12fab01ef1837996f90e12d
ciphertext: d1cf208440ca32057ed511b9baaa817b8036bb3e9ab4e4f1c729187ef6af
53d4a9e0bfb25404cb336efe28ee3d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f12fab01ef1837996f90e12c
ciphertext: 6f948abb01565f095d39819194a7076e85c33919882d7b6bc54e1814b275
5a50d814c6c6ca725b2b4f8b802099

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f12fab01ef1837996f90e12f
ciphertext: 455593d46404c2178a1e7a05431ad37ca35a3e2d43bf478952a2920a9c6e
fd1971624025344e0d9be6ad8bc7ec

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f12fab01ef1837996f90e129
ciphertext: 2fb5e7c44622de8549ee563a5aae857ffeb54a317b383c177d7aa0125e8b
67a4544eb008ea3966358aaf9f5edf

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 654ab19fdc95b8656cee07eeba21d837bdb965c4c10d3efd9023086b2ae324e4
skE: d64fe9010d3fd32114f5e60f326c60f782fa3ff56f71b9452e8d91a6f426a4cc
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 046ecd02480c6a5db13f3803e2d8182bb132fb8ad3ad26e038f50a9b1a2538d5a37
49795d4219789d539289ab91219e024b4ca43315153969437e8e7a1f1dc9e4b
pkE: 04ecae08130ce757348c5c1677553856e9b40249e65717a3765d9bfbb4cfcf8e805
12358941b6281dc64ebe783a21453e5e85584cea0a9471d0fb90a257ff8926d
enc: 04ecae08130ce757348c5c1677553856e9b40249e65717a3765d9bfbb4cfcf8e805
12358941b6281dc64ebe783a21453e5e85584cea0a9471d0fb90a257ff8926d
zz: c5421af7160bc5ba08d2892020d2ef9c783aacfead0202b55f9a03c6224afb5b
context: 00100001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: f72737c4c9cd2a79d82eee9c692f4faf2da53aa6a2495d1152f7d3e7bbebb9cb
key: 35286da66cce19bd9bc93f288904e23ff879d9320d32052a431d5bb29b98b651
nonce: 182f818b070636ab290b7336
exporterSecret:
b965c0577224e819d38b13f7f4890bd15d41ce3af550f1b7cd564a1bfa307ba4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 182f818b070636ab290b7336
ciphertext: 090ff66743ffe31efd8f631df5d3d9d4348ef607d043d5b7f2a616e243db
f6b35b57d17b35302cbb4eb265df07

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 182f818b070636ab290b7337
ciphertext: 68a0dfaaf7f891571f283a118e5593ff7b86c6760eb8577dd9a92bca77ae
8b3ac8a71b28dce9f91189f1b36fa8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 182f818b070636ab290b7334
ciphertext: b227afa2dd3864137143fe617e6dbf157a2ec4b9aeeb376af53b3deaefc5
594d95c67c3f5f7ecbb38c5357175f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 182f818b070636ab290b7332
ciphertext: a7691b3d044df3248fd4fd6abcd3c30589a49bebd8e127c0c15e65f2db30
6f9c4f8565ab815292582bed84c888

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 6134a52f8fb5d0413db51e54cb2eeb0b3ebabdcf291a18287542fd2ff8ccbb46
skS: d0fb888fcb2ae75f226bf076c9eb1945de61fafab67007f88f5fdc396c4c37ee
skE: f6a76c5f517811aee1bd6d296cc140ec14002b578eb8f52ca7ddbb0ce8184d8d
pkR: 04b12759de146e8bf8bfa8f8c1d5c79de6bc04d55f9289d7dbca3d6f7f452f57ffc
d68f37fadc1369d50b2fc7b1a896389ce5b4275a0bfc39d02430e7ebed2fa0c
pkS: 043283361eca4cb9965c487d5c4b31bc79baf264a415e90d7de2cfb8e3049cb76bd
345583d2f9da7ae558be5eac05d3f0e47783cefb765a87d124615724a7651fc
pkE: 04440cf592ffa724cf469663c0f27dfbf09be3dcf011fcafcc4cf263ec550ce5aba
e55a0ee6bdc175b69b26cfd00699a817d077073cfa36f1d845d8287191a0f0c
enc: 04440cf592ffa724cf469663c0f27dfbf09be3dcf011fcafcc4cf263ec550ce5aba
e55a0ee6bdc175b69b26cfd00699a817d077073cfa36f1d845d8287191a0f0c
zz: 9627ac86436a3d42569b0a00f18efb4006ed933c447c1e2380b31bc9aecfd5bf
context: 001000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: b46be90bfbd29ef1a494d6f48b02f548841625406e9fdcbd4ae7a9e3e53a9b60
key: a4ab15a3cbb9022efa58cca16b64474f3e45ec970329dc480a2b26e554659d75
nonce: f2e0d1dc7385f8f3f9276f7a
exporterSecret:
c0c5b279430b59303f6a0c19b66270fc63a041c4e2452d014abe75e9861d6605
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f2e0d1dc7385f8f3f9276f7a
ciphertext: b93f4121badc0913b2c06454ed93544c4f2d6f8202c1efd02918d4c1dc13
65989a4daa98f3002c8af88c42cf77

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f2e0d1dc7385f8f3f9276f7b
ciphertext: 941d2999f70921defc2602fbdfa5b39cdae5e6fe00b606a15d9adf0d2685
d9adf1ba85fe37060c6981cc2eff74

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f2e0d1dc7385f8f3f9276f78
ciphertext: 8dd3b4c153a1915e94efbecc709e808975d5244b383d4d2d16266a8b4ead
2940a389c63958da3c166537d08ef7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f2e0d1dc7385f8f3f9276f7e
ciphertext: d02b7216ca3cb394d18b2f650959a90f933b7df79705fb8655156fd409af
9136343b951afdf6ca311a262235d0

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: fa9d5864d5746d01f498aa4138753c12a56b45d55a2ec83217e1e0a87589374a
skS: 3bc0afdb8584331079ddfa1deba03d55503325c9dcc65884afa627533288117e
skE: 20349a95c704604cf6ab5ec4a948beac097820ab30aa83676bca1b9f591dfc04
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04dfdd4fd2bcc00498b61bf3ff2bfdfafedae70ff884a3a0508c526c91f8559d0b3
d98e2429a1861e2001c6b63c5361eff69a5e4fe54d8e95febad40068c45062b
pkS: 04383fe5c1e93324c270dc27e80b8b8526a0063802663a9d5c3f5bbb5c09152a9a2
0978a56f7755b13786b8a7634281d0f9a9e6c92e19fc4a4ee96fe2a26fd4406
pkE: 04bc728d4d1fc38a773441745873c2f4673f4d9023b58b268592d0c745943793f62
1f44fa0641b2eda59bcdf3c353a8a54e799775927584cc180e250c227abda4a
enc: 04bc728d4d1fc38a773441745873c2f4673f4d9023b58b268592d0c745943793f62
1f44fa0641b2eda59bcdf3c353a8a54e799775927584cc180e250c227abda4a
zz: b84782558607409251469490e8674ec2ee7ab068be5aceddf386aedf82ab7838
context: 00100001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 5a2f7424272c3a08447d0f39e0e72a63d61fcdc981366dc2471324f622d342d2
key: 887108061056f6a32d9b4975fc046bac7b4adc14c5d59784e59c4fe2d41b5744
nonce: e55905e6adfdbed7b4872717
exporterSecret:
0e0cac5418a81a5752f9033043eb0aefa9523c5570d29d56b62ec22bdf11a56d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e55905e6adfdbed7b4872717
ciphertext: 89916dbb7dfef2af85d7b3a922f56ff97ecc877f12bde824f82338a2f4c7
e4ab1c8d5125497bf2e535148422a6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e55905e6adfdbed7b4872716
ciphertext: 466d17fdf8f9af9db5e2711b4b6df621410586102a540bb530d28dd16fee
7adf184b6e6eee2b9b28e469e169c3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e55905e6adfdbed7b4872715
ciphertext: 3604a0d53adbf9e384a3633a06d3ab25ce37af8463823ed2723e29432d40
7716238bdbdd31d1a89fb8fa538469

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e55905e6adfdbed7b4872713
ciphertext: 26d3a8ff6f5ec2b214bb6faf5fd7a2d72c81bb99295ce5db7a4cdde6f10e
7d9ca64d155202acc05fb5d816765e

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01b3e33a2cf926ef496fff7e86a3743c23a9797c3bf99af8366ce22b3b0940fff1f
1934e4d0bd539e130bdc3ff5991d37bdf45fc73529fe9a2e00e138d376610c26a
skE: 00252116681dacf4e707e9881aff5496942a36e74185347df21ab9d647dfe2a910e
325b027ac3114335c038589d86a6a1a665498a5a6ea687ad5ddbd4258f273e2e7
pkR: 0400ec315d49eee4579d51967cb9cf2a848d918059769f530f0fcfb92342bbf00b5
61a55dc58fae5f8ef0fcf53e86514600b09787dc886afbbd682feb5cd3d1b3e671800be3
c0358bf880ba2435eada8a1d5ea3585ea920c29ae39a5cb035de057721b8fc07d0666d46
a6be634b257427404a19c7ebface8fa37da857bbef6fe04622d9627
pkE: 04018cb8773e67d760392738f6c623e7ec6c67f9b3ecd2fdbcea912e794abe74bc0
9c7453cd34c03066af58b699a0151d96411737ebca94bbc29c1c9085c7d2f43793a0191e
ffdb3b5f428059c7db5508d8bb3597df0477098e7578231570b7e9fb85696391c1117aec
6c5ea34dbfc34c535fbd42c350246bf093160e89463bb0ea650e36b
enc: 04018cb8773e67d760392738f6c623e7ec6c67f9b3ecd2fdbcea912e794abe74bc0
9c7453cd34c03066af58b699a0151d96411737ebca94bbc29c1c9085c7d2f43793a0191e
ffdb3b5f428059c7db5508d8bb3597df0477098e7578231570b7e9fb85696391c1117aec
6c5ea34dbfc34c535fbd42c350246bf093160e89463bb0ea650e36b
zz: e1dfc9abea0a02ec20bef7159cf2cd9049618bbbfa4c4182ce4ca85d95b20cc02e4c
b50697a33c002c34d8de230b694ced34538d4f79afd2bcc981480d684759
context: 001200030002008ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: e5eff28f7429a3e95cf44a45b6a82062959b11bc9b7f85264cd34bc6de12136a
3a385b9a9bb26fce21e038e176671c8c83a12e5062a1043c4dbb6e5acfe6e748
key: f108b5f5b47e3ef03a03c2b2cba0154d53033592877a2cf5b4beaf0f7b91959a
nonce: 49dd43ca5c2d9176a5e5df2a
exporterSecret: c76c811e401260f763f540a1982346d1087e2379921aea2815b333fa
23172e78ca5ee37730bc0dde79ed658bf84b837c7c2647320e1ae3b5e4bd4eed8f30870c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 49dd43ca5c2d9176a5e5df2a
ciphertext: 0ee862df2a7829b7ba67fe033cebeea80bed51cf9677c96273a83191a07c
67a7710586281bf945b36c1517a04e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 49dd43ca5c2d9176a5e5df2b
ciphertext: cc74da50bd1add07951b184df33237fc8de6eecc3bcd5e75fc4e9eead8b6
4000e44c4290a2084582d1cd6cd987

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 49dd43ca5c2d9176a5e5df28
ciphertext: 4a7844a39f25c6a1d98b15a795fdf739b0adcb47739bd4ba923f14b16256
d5b30bbed812d512d48a1d33fb4013

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 49dd43ca5c2d9176a5e5df2e
ciphertext: 14e504245942918ae8a51419987b7a18c2e0e92cc79a6dba83af2655fbfa
8125df9572059aa64480ef860b49f2

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 017ee8d2bb7dc4766d91596bc1fa741d03ac78c729258e9118c65a2b21d9fcb4249
b3854049a384c8c3c18387ae4d94b57e11407359d62cb5de0e7c2eeded7c5ee32
skE: 009c521217c269a1c94169f6bcd3b399903ea6d385b38d51eac1fa07a4aac06bc14
4613ba531e3377a817715d987fd63229e3adcaa1e585e3fe75ea8288a486ae3a8
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04009070038197aaa0221dc91ad4c638ce2e28ba901d9cf588f4dcec4ae243507f1
9bf14c835d442aa26a9ee6d14f69777ae92c6f3a80f29bdd24ec38972a23ce0e89a00f81
d57db61fb8f530c25fb9dd226bf57de3c914254baf5c57c2de46cded50e051531b0d5e7e
a57c26a4ab80bba58e1b862110ad67b505e8f1011e00ad3f23a0d43
pkE: 04013fb71b35ae40dded07b44ceb170eaa977f863d71fc1bfb04c3d659ed612b6e9
2a6b2ded3f279353d4cad5acb75347ce0019dc18a3d5cec356af19d426dc8e59a9b00ba5
02ddb35e33f9e55eca473e6cfebec86e4fe2411ea482bb6cd6980f61b5fb0be7f613fafc
8f63e035c9d7428ca6fa85a4b6a27d9abb2e120673adf197f33d303
enc: 04013fb71b35ae40dded07b44ceb170eaa977f863d71fc1bfb04c3d659ed612b6e9
2a6b2ded3f279353d4cad5acb75347ce0019dc18a3d5cec356af19d426dc8e59a9b00ba5
02ddb35e33f9e55eca473e6cfebec86e4fe2411ea482bb6cd6980f61b5fb0be7f613fafc
8f63e035c9d7428ca6fa85a4b6a27d9abb2e120673adf197f33d303
zz: 549640ce1478ada68bc61005c29b0fea816c5350dcd02ab99e73ec1cc0d2af7a0eed
d1367faa7d3f6f9b5892ac034a9bec13e65b8ac276eb7a3c169bb1f4ca0d
context: 0012000300020119d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: e3689312061fc1f9e2159bb93b4d1bd1f48d77ef52796b1e41b931bc5e37868a
c1715e33b25476412c7b9c9563aae4a827d36ea846e461aabe75c25b87812107
key: 53adaee3d7c7e87de7cc594140a85dc1d721d1f0f88af84d96d3f4d6248bbdbd
nonce: 85cce02475d9ae00f1118490
exporterSecret: 9b28e6580e93cb6621c04037f5c7b4157fa4b5d0a6d5081011668d51
c2e817539a8f14be34948f597ba8f195001066c4f6632ce556251bba0513a0b0d5476074
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 85cce02475d9ae00f1118490
ciphertext: 6d4cfb895172d678b06738dbcf3061048ad80b83eed4fe39b3228c7e5ee2
ae78f7a0cca0db323fd27affb0c7f2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 85cce02475d9ae00f1118491
ciphertext: 37072bbcdd63ecdfff53c236dc099de0f3b4641a04f73a6a91e6a441d0ff
018754e6413388753e8bd8bcdd2a0f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 85cce02475d9ae00f1118492
ciphertext: fef8048a3e13f98daae2ceb977b0558403401fc82879f6e2a81139ad269e
53c227062eb4e8630e13d98151203f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 85cce02475d9ae00f1118494
ciphertext: 54fd5d811c502e448920675ea4216c9f8d738b1682651bc3475ec1ba65bb
e983bb0b2cabc415d63309a7999b45

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00e4a39e9808aec7cf16708aeb13eaa70fd0bcb453534233836f3207d88c61af1c2
3a4a993687973b42d178c1789bee1656f01d463e86cad6758c79f817f680e26bf
skS: 01dd6f1ea81fbcb28da541d801edfa89e5648cc809b42cbe8b503caf6d7c5026a8b
d9ea058951b8b9eee10e095a1865ef26ef247a3e62c25062f3877ff0627711eca
skE: 0179c8ecb90db0cec33df6cf79fda902d4facfd55a1e26216e176769d149df8da12
d46f35f07c7cabd5613dc47826fc5b778f24a50381c4ed0a9b93cee969f32f735
pkR: 0400bd881c923366876ec86f5110ec695d2da0cd8b35e64adbd5a9b13fc6daa9daa
c5b38277b6cd791fd6b47deab09815492426f373ead722b2ea7257b9e110681ec1001800
806a1c5f656bb354333c001d20a7639e5749fb3bc1a209f00e512752bceffa60e771926c
e9d6972bb3abeaf6d314b09d3c0ae69452dd61db2b84a21d70402dc
pkS: 040162d338cc04cf8f7aa40bf50efdef65fd17d561a22e387e833fa71408a9a3a7e
44900964544c58ce2e3e444a4622fafdaa0ce72d39266b6aae61d01879783bd5d910063e
c49234436b959148f8220e583774298e5dbd28be96be0c4f754ac93a10306c72495a8447
2d08376547d5fec4da477d316c4f6810cd97a9e97e792a06745fbc8
pkE: 040131079c4cbd0f4ee58ccf0f6cdefc6cd29470c0502f4852b84fbcd8ebc4aa5bf
7b0591372e290fe8d204c26342e27c4b6d6a5e6f8a81339328f46062b9a606028f701f23
f3ae4a48c0f90aa716fb4953e24e56f84b14a865cfbbf6ec9ce51e43504670cd2efbba2f
c8339ae40fac6a5e1d4e18d9d076dde50c881492921d4c583428766
enc: 040131079c4cbd0f4ee58ccf0f6cdefc6cd29470c0502f4852b84fbcd8ebc4aa5bf
7b0591372e290fe8d204c26342e27c4b6d6a5e6f8a81339328f46062b9a606028f701f23
f3ae4a48c0f90aa716fb4953e24e56f84b14a865cfbbf6ec9ce51e43504670cd2efbba2f
c8339ae40fac6a5e1d4e18d9d076dde50c881492921d4c583428766
zz: afecd208b4c8afe4edc325ad1ec4da83d5911b25054948cf6a6fe3b6f88de22febbf
79eb40fa7793c02431c4f4a2019b08c55b63bbe536f446710f0b40407d10
context: 001200030002028ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 10992ace2e26b84680077cb96e277ed62e22423ac9554e807b33357664be2e69
486a607916e2deaa2cadc0fc17deca089adfb1795dae25154db38ca71d76e2c7
key: c5a500e60f78fc9005f61fb8da7857c5884faf13d53ebbbf9883fbc605c36b5a
nonce: 52fb5d32f6e1f322a21ea824
exporterSecret: ed0ab2e6790caf174fdc9ac0d0322021ad7130dc1992b6b1970bf423
70245fbabf42dde1a6b7f159eeb052b7ac81071d1470e79ea8ce9552c9c4d05f183102fa
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 52fb5d32f6e1f322a21ea824
ciphertext: e6bbf97c7a233cbc520279b4fa0f9e5d0c5dbe14f993d7a9163c61ba3b5d
3f977a48af10cf592c4d572bb2881c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 52fb5d32f6e1f322a21ea825
ciphertext: a1ca97d0dc69709014422b18e9797003e9d294b23ecee192f163baf58302
4d3f212f12858e8bf6d35289ba6fb7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 52fb5d32f6e1f322a21ea826
ciphertext: c7ec1ca69653cc81b3a4ad4ab10c3ce471cd5381f8d6961d97bb6f6279d4
8352ee65f43224556d41e3c2bcca70

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 52fb5d32f6e1f322a21ea820
ciphertext: 90d3d47bbc91115742d37947c8c7b21ee267943fd500e1b937b58071ec48
cefb266fe830a12410f65fdf2b657f

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00dcca4c7aad3a047a5d0c579dce56d45a6ef7446055ef19d4295dff1b8d1586f95
e09052f733c5d1c9fa8bb7eab289cc3c5bb23e55559606a7b509d56bd660a63d0
skS: 002a28ddb89ecbb9af391e31185cdaf7a4683c9bf3f950866b73e65cae7f769a849
a792b23c65266cda967208a6f7d741ce06b9a5b206a1c670a36a02c0b2d62bbc5
skE: 00a69a328f366433eb173d1cd308627e6733d7b52d88745eb8bd63a4d4959d6ff82
389a1ead33fa9816afcb348532d78d41e1444f9f1aa945cdfc4f4bb98c8514722
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0400475fd0db79dacda40f43684ccc8a3397689135f422388905a95f7fc4357fad0
ef3dec49c98a5aaa722457e4ee51d4eca72845b2d0580a8e77ab5086c3a9c6edede00c5b
fa1b71a8c8ba3672952e5ceebc0446df94c96cc0051faa671158d5c9c86a05797c3ca6cc
c19173b09bf2fe9b8e052f4ffecc871df03dc1da15b00cb1bfaa003
pkS: 040031d4c9313147b1b3e76ae4721a1fd12b8ff0096f5b4301e062e52d59d5cbebf
1826b424e4ce29ebf726fd67425451506f3a38fe9b5d38c967ef4f03d9b4ae55e4901449
a96bc684065b5e10e7852b43b7fbba72e3ecd3daf740c1b32289194beed37aa233c70ef8
ae5cccd2ff65cbce812135e7dc5771b37506f1671f98dede8641dd8
pkE: 04009099465afd901ba69bf88f870b57c073d334980469cc3cba70469bdfa01ee5c
b473fbfbc2b0a043ca5964aebfd98f8ac86a102807a5aaa6be5e15839781c48c7fe018dd
0ac7fb602b0481f7c9a3d8b3dba2f4f840b0a417f0aa3a03e665cc852cfd9e091662f89a
7db1f90ae3377be8dd7ab0ea1e00c524ed22002ba9a802adc66c551
enc: 04009099465afd901ba69bf88f870b57c073d334980469cc3cba70469bdfa01ee5c
b473fbfbc2b0a043ca5964aebfd98f8ac86a102807a5aaa6be5e15839781c48c7fe018dd
0ac7fb602b0481f7c9a3d8b3dba2f4f840b0a417f0aa3a03e665cc852cfd9e091662f89a
7db1f90ae3377be8dd7ab0ea1e00c524ed22002ba9a802adc66c551
zz: 2e2b048850e14fd394bd50c4958415e2383ae178ab952edb5382de5fff0418416091
b5ae209937552c3462aaeb10daebec1808e4b91590780fe1f71f2350fbb4
context: 0012000300020319d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 9c4e164594f78fee0e4d831f66d27089182053d4e061b6e9ae6201e8717e7e2b
ab915484af139dbd14268ced341c368954430e146bf496fb96297fbe1e0b5012
key: eb051e3567ad0bb649352cf3b6c0a9109ec83b017e8cd4e9f38f7d0e412329cd
nonce: 03d8774ad04a46e2ce48bf90
exporterSecret: 27f9ed77b2a5716a825249280aeb8f122b79e89b7f4bc2f4ef888953
5d5818b276380aac8fc5edc795a541118c9f2e171ee98fafbb850b35ef089cb59cd1042c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 03d8774ad04a46e2ce48bf90
ciphertext: f8cccd94529f0182adc696e4ac638301d3660c9dccb1d30e293cf0d44c58
1254ef0e6c85364eef3dc308c94cdd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 03d8774ad04a46e2ce48bf91
ciphertext: e3f7c5c3de0e5fce026e6f60fbc6d4d4263ef5473004b1ae5fffcdb8a0d7
801f757f032b9b547afa0c1b5067f1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 03d8774ad04a46e2ce48bf92
ciphertext: 3ea46fc37f4941d15f524cbd5f2a91356efab2684b29ff799c180bd0b5a0
e8ec0059c203805757579d3523f8c5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 03d8774ad04a46e2ce48bf94
ciphertext: 09a2f6d90bf54d484a514d20fe4a6b6ce587282a36d253dd7242dab64efc
146356adb672546817443233a86afe

~~~
