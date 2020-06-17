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
    title: "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack"
    target: https://eprint.iacr.org/2001/108
    date: 2001
    author:
      -
        ins: R. Cramer
        name: Ronald Cramer
      -
        ins: V. Shoup
        name: Victor Shoup

  S01:
    title: "A proposal for an ISO standard for public key encryption (version 2.1)"
    target: https://eprint.iacr.org/2001/112
    date: 2001
    author:
      -
        ins: V. Shoup
        name: Victor Shoup

  GAP:
    title: "The Gap-Problems - a New Class of Problems for the Security of Cryptographic Schemes"
    target: https://link.springer.com/content/pdf/10.1007/3-540-44586-2_8.pdf
    date: 2001
    author:
      -
        ins: T. Okamoto
        name: Tatsuaki Okamoto
      -
        ins: D. Pointcheval
        name: David Pointcheval
    seriesinfo:
      ISBN: 978-3-540-44586-9

  ANSI:
    title: "ANSI X9.63 Public Key Cryptography for the Financial Services Industry -- Key Agreement and Key Transport Using Elliptic Curve Cryptography"
    date: 2001
    author:
      -
        ins:
        org: American National Standards Institute

  IEEE:
    title: IEEE 1363a, Standard Specifications for Public Key Cryptography - Amendment 1 -- Additional Techniques"
    date: 2004
    author:
      -
        ins:
        org: Institute of Electrical and Electronics Engineers

  ISO:
    title: "ISO/IEC 18033-2, Information Technology - Security Techniques - Encryption Algorithms - Part 2 -- Asymmetric Ciphers"
    date: 2006
    author:
      -
        ins:
        org: International Organization for Standardization / International Electrotechnical Commission

  SECG:
    title: "Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2"
    target: https://secg.org/sec1-v2.pdf
    date: 2009

  HPKEAnalysis:
    title: "An Analysis of Hybrid Public Key Encryption"
    target: https://eprint.iacr.org/2020/243.pdf
    date: 2020
    author:
      -
        ins: B. Lipp
        name: Benjamin Lipp
        org: INRIA Paris

  MAEA10:
    title: "A Comparison of the Standardized Versions of ECIES"
    target: https://ieeexplore.ieee.org/abstract/document/5604194/
    date: 2010
    author:
      -
        ins: V. Gayoso Martinez
        name: V. Gayoso Martinez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: F. Hernandez Alvarez
        name: F. Hernandez Alvarez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: L. Hernandez Encinas
        name: L. Hernandez Encinas
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: C. Sanchez Avila
        name: C. Sanchez Avila
        org: Polytechnic University, Madrid, Spain

  BNT19:
    title: "Nonces Are Noticed: AEAD Revisited"
    target: http://dx.doi.org/10.1007/978-3-030-26948-7_9
    date: 2019
    author:
      -
        ins: M. Bellare
        name: Mihir Bellare
        org: University of California, San Diego
      -
        ins: R. Ng
        name: Ruth Ng
        org: University of California, San Diego
      -
        ins: B. Tackmann
        name: Björn Tackmann
        org: IBM Research

  JKR96:
    title: "Designated Verifier Proofs and Their Applications"
    target: https://doi.org/10.1007%2F3-540-49677-7_30
    date: 1996
    author:
      -
        ins: M. Jakobsson
        name: Markus Jakobsson
        org: University of California, San Diego
      -
        ins: K. Sako
        name: Kazue Sako
        org: NEC Corporation
      -
        ins: R. Impagliazzo
        name: Russell Impagliazzo
        org: University of California, San Diego

  TestVectors:
    title: "HPKE Test Vectors"
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/f0be13a4cf8fa4f39e1cb396d42b9a234ad85017/test-vectors.json
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
    author:
      -
        ins: Y. Dodis
        name: Yevgeniy Dodis
        org: Department of Computer Science, New York University
      -
        ins: T. Ristenpart
        name: Thomas Ristenpart
        org: Department of Computer Sciences, University of Wisconsin–Madison
      -
        ins: J. Steinberger
        name: John Steinberger
        org: Institute of Theoretical Computer Science, Tsinghua University
      -
        ins: S. Tessaro
        name: Stefano Tessaro
        org: CSAIL, Massachusetts Institute of Technology

--- abstract

This document describes a scheme for hybrid public-key encryption
(HPKE).  This scheme provides authenticated public key encryption of
arbitrary-sized plaintexts for a recipient public key. HPKE works
for any combination of an asymmetric key encapsulation mechanism
(KEM), key derivation function (KDF), and authenticated encryption
with additional data (AEAD) encryption function. We provide
instantiations of the scheme using widely-used and efficient
primitives, such as Elliptic Curve Diffie-Hellman key agreement,
HKDF, and SHA2.

--- middle

# Introduction

Encryption schemes that combine asymmetric and symmetric algorithms have been
specified and practiced since the early days of public-key cryptography, e.g.,
{{?RFC1113}}. Combining the two yields the key management advantages of asymmetric
cryptography and the performance benefits of symmetric cryptography. The traditional
combination has been "encrypt the symmetric key with the public key." "Hybrid"
public-key encryption schemes (HPKE), specified here, take a different approach:
"generate the symmetric key and its encapsulation with the public key."
Specifically, encrypted messages convey an encryption key encapsulated with a
public-key scheme, along with one or more arbitrary-sized ciphertexts encrypted
using that key. This type of public key encryption has many applications in
practice, for example:

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
implemented. The HPKE construction defined herein is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions about
the underlying primitives {{HPKEAnalysis}}. A summary of this analysis is in
{{sec-properties}}.

# Requirements Notation

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP14 {{!RFC2119}} {{!RFC8174}}  when, and only when, they appear in
all capitals, as shown here.

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- `(skX, pkX)`: A KEM key pair used in role X; `skX` is the private
  key and `pkX` is the public key.
- `pk(skX)`: The public key corresponding to private key `skX`.
- Sender (S): Role of entity which sends an encrypted message.
- Recipient (R): Role of entity which receives an encrypted message.
- Ephemeral (E): Role of a fresh random value meant for one-time use.
- I2OSP and OS2IP: Convert a byte string to and from a non-negative integer as
  described in {{!RFC8017}}. Note that these functions operate on byte strings
  in big-endian byte order.
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`.
- `zero(n)`: An all-zero byte string of length `n` bytes. `zero(4) =
  0x00000000` and `zero(0)` is the empty byte string.
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - DeriveKeyPair(ikm): Derive a key pair `(skX, pkX)` from the byte string `ikm`,
    where `ikm` SHOULD have at least `Nsk` bytes of entropy (see
    {{derive-key-pair}} for discussion)
  - Serialize(pk): Produce a byte string of length `Npk` encoding the
    public key `pk`
  - Deserialize(enc): Parse the byte string `enc` of length `Npk` to recover a
    public key
  - Encap(pk): Generate an ephemeral, fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to pk
  - Decap(enc, sk): Use the private key `sk` to recover the ephemeral
    symmetric key (the KEM shared secret) from its encapsulated representation `enc`
  - AuthEncap(pkR, skS) (optional): Same as Encap(), but the outputs
    encode an assurance that the KEM shared secret key was generated by the
    holder of the private key `skS`
  - AuthDecap(skR, pkS) (optional): Same as Decap(), but the recipient
    is assured that the KEM shared secret was generated by the holder of
    the private key `skS`
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
    `nonce`, yielding ciphertext and tag `ct` or the error value
    `NonceOverflowError`
  - Open(key, nonce, aad, ct): Decrypt ciphertext `ct` using
    associated data `aad` with secret key `key` and nonce `nonce`,
    returning plaintext message `pt` or the error values `OpenError` or
    `NonceOverflowError`
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
  labeledInfo = concat(I2OSP(L, 2), "RFCXXXX ", label, info)
  return Expand(PRK, labeledInfo, L)
~~~

\[\[RFC editor: please change "RFCXXXX" to the correct number before publication.]]

## DH-Based KEM

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- DeriveKeyPair(ikm): Derive a key pair `(skX, pkX)` from the byte string `ikm`,
  where `ikm` SHOULD have at least `Nsk` bytes of entropy (see
  {{derive-key-pair}} for discussion)
- DH(sk, pk): Perform a non-interactive DH exchange using the
  private key sk and public key pk to produce a Diffie-Hellman
  shared secret of length Ndh
- Serialize(pk): Produce a byte string of length Npk
  encoding the public key `pk`
- Deserialize(enc): Parse a byte string of length Npk to recover a
  public key (note: this function can fail)
- Ndh: The length in bytes of a Diffie-Hellman shared secret produced
  by the DH function of this KEM
- Nsk: The length in bytes of a Diffie-Hellman private key

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF:

~~~
def ExtractAndExpand(dh, kemContext):
  prk = LabeledExtract(zero(0), "GROUP-dh", dh)
  return LabeledExpand(prk, "GROUP-prk", kemContext, Nzz)

def Encap(pkR):
  skE, pkE = DeriveKeyPair(random(Nsk))
  dh = DH(skE, pkR)
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def Decap(enc, skR):
  pkE = Deserialize(enc)
  dh = DH(skR, pkE)

  pkRm = Serialize(pk(skR))
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz

def AuthEncap(pkR, skS):
  skE, pkE = DeriveKeyPair(random(Nsk))
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  pkSm = Serialize(pk(skS))
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = Deserialize(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Serialize(pk(skR))
  pkSm = Serialize(pkS)
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz
~~~

The string "GROUP" used in the `ExtractAndExpand` function is equal to the
ASCII-encoded name of the underlying DHKEM group. The table below lists the values
for this parameter for all DHKEM variants specified in this document. For example,
the `LabeledExtract` label for DHKEM(P-256, HKDF-SHA256) uses the string "P256-dh".

| DHKEM  | Group Name |
|:-------|:---------- |
| DHKEM(P-256, HKDF-SHA256)  | "P256"   |
| DHKEM(P-384, HKDF-SHA384)  | "P384"   |
| DHKEM(P-521, HKDF-SHA512)  | "P521"   |
| DHKEM(X25519, HKDF-SHA256) | "X25519" |
| DHKEM(X448, HKDF-SHA512)   | "X448"   |

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

# Hybrid Public Key Encryption {#hpke}

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
possession of a KEM private key. Both authenticated variants contribute
additional keying material to the encryption operation. The following one-byte
values will be used to distinguish between modes:

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
plaintexts. It also has an interface for exporting secret values,
as described in {{hpke-export}}. See {{hpke-dem}} for a description
of this structure and its interfaces. As is standard with AEAD interfaces,
HPKE decryption fails when the underlying AEAD decryption fails.

The constructions described here presume that the relevant non-private
parameters (`enc`, `pskID`, etc.) are transported between the sender and the
recipient by some application making use of HPKE. Moreover, a recipient with more
than one public key needs some way of determining which of its public keys was
used for the encapsulation operation. As an example, applications may send this
information alongside a ciphertext from sender to receiver. Specification of
such a mechanism is left to the application. See {{message-encoding}} for more
details.

The procedures described in this session are laid out in a
Python-like pseudocode.  The algorithms in use are left implicit.

## Creating the Encryption Context

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context. The key schedule inputs are as follows:

* `mode` - A one-byte value indicating the HPKE mode, defined in {{hpke}}.
* `zz` - A KEM shared secret generated for this transaction
* `info` - Application-supplied information (optional; default value
  "") of maximum length 65535 bytes.
* `psk` - A pre-shared secret held by both the sender
  and the recipient (optional; default value `zero(Nh)`) of maximum
  length 255 bytes.
* `pskID` - An identifier for the PSK (optional; default value `zero(0)`)
  of maximum length 65535 bytes.
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
provided, then the recipient is assured that the sender held the
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

  ciphersuite = concat(I2OSP(kem_id, 2),
                       I2OSP(kdf_id, 2),
                       I2OSP(aead_id, 2))
  pskID_hash = LabeledExtract(zero(0), "pskID_hash", pskID)
  info_hash = LabeledExtract(zero(0), "info_hash", info)
  key_schedule_context = concat(ciphersuite, mode, pskID_hash, info_hash)

  psk_hash = LabeledExtract(zero(0), "psk_hash", psk)

  secret = LabeledExtract(psk_hash, "secret", zz)
  key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  nonce = LabeledExpand(secret, "nonce", key_schedule_context, Nn)
  exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)

  return Context(key, nonce, 0, exporter_secret)
~~~~~

See {{hpke-dem}} for a description of the Context output.

Note that the `key_schedule_context` construction in the KeySchedule procedure is
equivalent to serializing a structure of the following form in the TLS presentation
syntax:

~~~~~
struct {
    uint16 kem_id;
    uint16 kdf_id;
    uint16 aead_id;
    uint8 mode;
    opaque pskID_hash[Nh];
    opaque info_hash[Nh];
} KeyScheduleContext;
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
secret, so if the recipient is one, then the sender is the other
with overwhelming probability.

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
decryption, this allows applications to amortize the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this decryption must be
stateful. Each of the setup procedures above produces a context object
that stores the required state:

* The AEAD algorithm in use
* The key to be used with the AEAD algorithm
* A base nonce value
* A sequence number (initially 0)
* An exporter secret (see {{hpke-export}})

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
in use.  The sender's context MUST NOT be used for decryption. Similarly,
the recipient's context MUST NOT be used for encryption. Higher-level
protocols re-using the HPKE key exchange for more general purposes can
derive separate keying material as needed using use the Export interface;
see {{hpke-export}} for more details.

It is up to the application to ensure that encryptions and
decryptions are done in the proper sequence, so that encryption
and decryption nonces align. If a Seal or Open operation would cause the `seq`
field to overflow, then the implementation MUST return an error. (In the
pseudocode below, `IncrementSeq` fails with an error when `seq` overflows,
which causes `Context.Seal` and `Context.Open` to fail accordingly.) Note that
the internal Seal and Open calls inside correspond to the context's AEAD
algorithm.

~~~~~
def Context.ComputeNonce(seq):
  encSeq = I2OSP(seq, Nn)
  return xor(self.nonce, encSeq)

def Context.IncrementSeq():
  if self.seq >= (1 << (8*Nn)) - 1:
    return NonceOverflowError
  self.seq += 1

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
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
  enc, ctx = Setup<MODE>S(pkR, info, ...)
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
| 0x0020 | DHKEM(X25519, HKDF-SHA256) | 32   | 32   | 32  | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64   | 56   | 56  | 56  | {{?RFC7748}}, {{?RFC5869}}   |

### Serialize/Deserialize

For P-256, P-384 and P-521, the Serialize function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}. The Deserialize function performs the
uncompressed Octet-String-to-Elliptic-Curve-Point conversion.

For X25519 and X448, the Serialize and Deserialize functions
are the identity function, since these curves already use fixed-length byte
strings for public keys.

Some deserialized public keys MUST be validated before they can be used. See
{{validation}} for specifics.

### DeriveKeyPair {#derive-key-pair}

The keys that DeriveKeyPair produces have only as much entropy as the provided
input keying material. For a given KEM, the IKM given to DeriveKeyPair SHOULD
have length at least `Nsk`, and SHOULD have at least `Nsk` bytes of entropy.

All invocations of KDF functions (such as `LabeledExtract` or `Expand`) in any
DHKEM's DeriveKeyPair function use the DHKEM's associated KDF (as opposed to
the ciphersuite's KDF).

For P-256, P-384 and P-521, the DeriveKeyPair function of the KEM performs
rejection sampling over field elements:

~~~
def DeriveKeyPair(ikm):
  prk = LabeledExtract(zero(0), desc, ikm)
  sk = 0
  counter = 1
  while sk == 0 or sk >= order:
    label = concat("candidate ", I2OSP(counter, 1))
    bytes = Expand(prk, label, Nsk)
    bytes[0] = bytes[0] & bitmask
    sk = OS2IP(bytes)
    counter = counter + 1
  return (sk, pk(sk))
~~~

where `desc` is "p-256", "p-384", or "p-521", depending on the curve being
used; `order` is the order of the curve being used (this can be found in
section D.1.2 of {{NISTCurves}}); and `bitmask` is defined to be 0xFF for P-256
and P-384, and 0x01 for P-521.

For X25519 and X448, the DeriveKeyPair function applies a KDF to the input:

~~~
def DeriveKeyPair(ikm):
  prk = LabeledExtract(zero(0), desc, ikm)
  sk = Expand(prk, zero(0), Nsk)
  return (sk, pk(sk))
~~~

where `desc` is "x25519" or "x448", depending on the curve being used.

### Validation of Inputs and Outputs {#validation}

The following public keys are subject to validation if the group
requires public key validation: the sender MUST validate the recipient's
public key `pkR`; the recipient MUST validate the ephemeral public key
`pkE`; in authenticated modes, the recipient MUST validate the sender's
static public key `pkS`.

For P-256, P-384 and P-521, senders and recipients MUST perform partial
public-key validation on all public key inputs, as defined in section 5.6.2.3.4
of {{keyagreement}}. This includes checking that the coordinates are in the
correct range, that the point is on the curve, and that the point is not the
point at infinity. Additionally, senders and recipients MUST ensure the
Diffie-Hellman shared secret is not the point at infinity.

For X25519 and X448, validation of public keys is not required. Senders and
recipients MUST check whether the Diffie-Hellman shared secret is the all-zero
value and abort if so, as described in {{?RFC7748}}.

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
{{kdf-ids}} and {{kem-ids}}) satisfy these properties when used as specified.

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
depend explicitly on the KEM public key `pkR` and the encapsulated key `enc`,
as observed in {{S01}}. The KEM shared secret returned by AuthEncap and AuthDecap
MUST explicitly depend on the KEM public keys `pkR` and `pkS` and the encapsulated
key `enc`. This is usually implemented by including these values explicitly into
the context of the key derivation function used to compute the KEM shared
secret. This is also how DHKEM meets the requirement.

## Security Requirements on a KDF {#kdf-choice}

The choice of the KDF for the remainder of HPKE SHOULD be made based on
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
enc, ciphertext)` before, it would now send `(enc2, ciphertext2, enc, ciphertext)`,
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

For example, using DHKEM(X25519, HKDF-SHA256) and AES-128-GCM, this would produce
a 48-byte signature comprising a 32-byte ephemeral X25519 key and a 16-byte GCM tag.

To verify such a signature, the recipient performs the corresponding HPKE setup
and calls Open with the provided ciphertext.  If the AEAD authentication passes,
then the signature is valid.

This scheme re-uses the authentication scheme underlying the AEAD algorithm in
use, while using the KEM to establish a one-time authentication key from a pair
of KEM public keys.

# Message Encoding {#message-encoding}

This document does not specify a wire format encoding for HPKE messages. Applications
that adopt HPKE must therefore specify an unambiguous encoding mechanism which includes,
minimally: the encapsulated value `enc`, ciphertext value(s) (and order if there are
multiple), and any info values that are not implicit. One example of a non-implicit value
is receiver public key used for encapsulation, which may be needed if a receiver
has more than one public key.

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

# Acknowledgements

This document benefited greatly from analysis done by Benjamin Lipp. The authors
would also like to thank
David Benjamin,
Benjamin Beurdouche,
Frank Denis,
Kevin Jacobs,
Michael Rosenberg,
Michael Scott,
Raphael Robert,
Steven Valdez,
Riad Wahby,
and other contributors in the CFRG for helpful feedback that improved this document.

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
skRm: 919f0e1b7c361d1e5a3d0086ba94edeb6d2df9f756654741731f4e84cb813bdb
skEm: 232ce0da9fd45b8d500781a5ee1b0a2cf64411dd08d6442400ab05a4d29733a8
pkRm: ac511615dee12b2e11170f1272c3972e6e2268d8fb05fc93c6b008065f61f22f
pkEm: ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258
enc: ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258
zz: 44807c99177b0f3761d66f422945a21317a1532ca038e976594487a6a7e58fbf
key_schedule_context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: c104521df56de97b517165011f09e0ea2a36b9af339a9de402c8b88547c8b67e
key: e34afc8f8f4c2906b310d8e4e4d526f0
nonce: 2764228860619e140920c7d7
exporterSecret:
93c6a28ec7af55f669612d5d64fe680ae38ca88d14fb6ecba647606eee668124
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2764228860619e140920c7d7
ciphertext: 1811cf5d39f857f80175f96ca4d3600bfb0585e4ce119bc46396da4b3719
66a358924e5a97a7b53ea255971f6b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2764228860619e140920c7d6
ciphertext: 2ed9ff66c33bad2f7c0326881f05aa9616ccba13bdb126a0d2a5a3dfa6b9
5bd4de78a98ff64c1fb64b366074d4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2764228860619e140920c7d5
ciphertext: 4bfc8da6f1da808be2c1c141e864fe536bd1e9c4e01376cd383370b80954
38a06f372e663739b30af9355da8a3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2764228860619e140920c7d3
ciphertext: 6314e60548cfdc30552303be4cb19875e335554bce186e1b41f9d15b4b4a
4af77d68c09ebf883a9cbb51f3be9d

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 37ee1a809e4672e8bb05f2b5ad59670d66393691c7eb72eb4ab68e2ee4c0e063
skEm: bbdd3185819ae4738a4b32ef1f0b8821523b3c209f79348ec65e32bf5faec98c
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 737e27e8da876cbc84fea54d2d923cd8831ece529437fd19f9c89b6522081c21
pkEm: 4ae5bdc205be146b4b77de12700a2cb3505b531f87f553c3c1a00691bf115e11
enc: 4ae5bdc205be146b4b77de12700a2cb3505b531f87f553c3c1a00691bf115e11
zz: 3c9c6213ce6faeb71df7c9af5f4b0fbe4598eca402006919f0abc48acd83c456
key_schedule_context: 00200001000101535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 29c12f0a81f1e3ee351b4d8ee395f57cd3da846a093a18a9326857b6e96d4123
key: e45c96c0f571dca743c84d0f236f9766
nonce: 0ffffebb7021e549cf507c3d
exporterSecret:
ddc6b38e2cd081a8474df90e5dda88055df7e0617e0ef7ba397684d72b33301a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 0ffffebb7021e549cf507c3d
ciphertext: 3b1d7ce76f47c5944640238d755a25bdabf6c2d5df4f9d596cdfc2ba854f
52d1d068993cdd39ac594a9141ac2e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 0ffffebb7021e549cf507c3c
ciphertext: e259150937dfaa7de3caa06edf4f3f22fc52d1538229b509f37f23df5e20
eabc424bc6af3fb6a71b5debfbfb50

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 0ffffebb7021e549cf507c3f
ciphertext: 8b299ce4699bf3eb8a128d53a0757669d9bfeeaade4346e6c5f131ac191d
2064cbd3ae7908fae1c8e1d6e22328

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 0ffffebb7021e549cf507c39
ciphertext: 9d4acc7f806d4d9491c6bf9583464d0e9d6dc3957e91d47054d8d236b06e
e8e9e60e1651bfa6a2ec22a3d85bda

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 04e212d132552363f6f5f354f75b9ee81cd0e23684c03ae4600b95bfba1682d0
skSm: 1ba133783bd84f10b73593070d747aae2a7407366fa313c46f50ff1a2ec35a7b
skEm: 42bc58e9a5f2eb1d0fafc329d5f440b80f1bd1d92f824a7af024fb809ea42853
pkRm: d09b37cb6524d9b9256f63662be269092b399c6e2576a5b77f89979cae311678
pkSm: 688cb65e180e0b76763d158e00b20ab150c4c43a7f44c438f2c6092967bcab4d
pkEm: fd5527ab9bc6725cca58e9895d2e77c8812ec1b3777b8be44cf4bd1e37edcc02
enc: fd5527ab9bc6725cca58e9895d2e77c8812ec1b3777b8be44cf4bd1e37edcc02
zz: ae09526a7b024d1c3b862f16be5a600064cfce046ce2e5194e3a368b8be2ae44
key_schedule_context: 002000010001025d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 908157049aae389b306f213db6f101c071ef4becd21b0d43cd5948cc12b51b1b
key: 63e5e35f14939f45566fdaf5dfc16f12
nonce: 58d7aee147ded72130f03902
exporterSecret:
9f465ff887a7f755836dd277bfe8044fbef77591161cd21a3aabf6b16cdf7c59
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 58d7aee147ded72130f03902
ciphertext: 72958cb0225e185e48a707217d6282e5a04521592eaaea4f7c93e74d5dab
3d7b7a8a7421f379c79d93d01b11c3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 58d7aee147ded72130f03903
ciphertext: 01ccfd7e2229f50b2f6380e7250c0e68623857d93ef6032916d810c1ac6f
bff0c454cc3da4044247339e6a5aa5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 58d7aee147ded72130f03900
ciphertext: 8b62bc4aea1cf124c8eea2d834cfaf1ab9a0d494acf590ae0c9600e7db1f
5fe627878f871a2f7ba907072f2a94

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 58d7aee147ded72130f03906
ciphertext: 8388a826adceea21f8623b417da21fe11179b8d0ff0a12de7342ab70f937
e1a4fa2ce17df61d0fd5d8e5e584ee

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 0d39d3bc608a07d381e3ed6fb2811f79f4a61e2bd98eca7898a14952ca310596
skSm: 7aba2dc2680eaea7bf52d76baaceed7576b0f4a1a43b04af8763500693a179d8
skEm: 52936c846aa86991605b4b0089023e489c998057ae698bb0e00ea46d8eb97ea8
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 87fd374667d901ddaaa4f54606e611828a7b61e313f2611f5e8c08a4bd229d40
pkSm: 957a9377cecca77bf53e684e88a6438e29b95b59967e17acbf06162686844c4a
pkEm: e8c603070c1db26cddabb41a11cb6a9f511ce79d5de3ecfffd8a025cae3e1247
enc: e8c603070c1db26cddabb41a11cb6a9f511ce79d5de3ecfffd8a025cae3e1247
zz: a8ae6464573fe151b08c94f018bf34a1fa1da17edc63d563bd51b02348cfa2f5
key_schedule_context: 00200001000103535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 2135d5a7865da96766782effcf64dbc6212f3721f30f7f4ea0f70c4c236753c8
key: 7905d70c70294c2c4d9edac553409030
nonce: 71aab972a7e4e0571324b137
exporterSecret:
723093cbbd0723a8c4ee67b2cf8515dc02ac4513b1cea53a75bcb454b2928611
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 71aab972a7e4e0571324b137
ciphertext: ceec7a558299e5e6218f485296b8353946eb032c750746533c611fab65d2
c8b71d41d57d1d4f8251517752ec15

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 71aab972a7e4e0571324b136
ciphertext: 8e98a8499a71baa1fbb6c02d52e97e72f3fdf0e66811664905312f166423
7b705eddbcce1d7f4b4182934e8089

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 71aab972a7e4e0571324b135
ciphertext: 81296873158f4ab447cd44be5d51efcb34618db1753b2df2d1ff6bd9227b
a8f42b74ee4b5c7a51d69ca5f30f41

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 71aab972a7e4e0571324b133
ciphertext: 44610668fee685ae1498e8490f59ae07fc10850a795e4f7e5ebd2df1ea45
ef30a85cc62e37d9771774d336e726

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: c474c6aab06e9d8d16912593f425dac89b3dd2d788d6b08631538591b70d9395
skEm: 55672de8afcc00aa3397b066123c0309e1c377bcdd0eca38838e330aa92e382c
pkRm: aff5d865a24e14cce0fd0a2212571b733027611418ca2ac6aff949e5f0c83e76
pkEm: 7e0a04d4be6c6a2936028337ebb6afad24f79cc23b105958ec9a7086826fe81d
enc: 7e0a04d4be6c6a2936028337ebb6afad24f79cc23b105958ec9a7086826fe81d
zz: a28dba903fe26d4de1d9760a7560e1f360510be316055645ee75149363fcc9a2
key_schedule_context: 002000010003005d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 1d89e0b49da2ca20a186b99ef5bfd41ceefa0a38652a0907b811d4493ee97ac6
key: 2e380e1200934ddfebf42017f731365e7bee44f3b19d5884eda302cc3d2f345c
nonce: 372867254b4044c7be47f312
exporterSecret:
1f519097b50549e455ea9396dc03098253d1a8c0e6ec8805b417f525382eb6ef
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 372867254b4044c7be47f312
ciphertext: f2d59922668b324a878c55391e7932c9b6f3efab5006a0d70f05ba467103
ce757a087f4f75bad47ea3715f07a6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 372867254b4044c7be47f313
ciphertext: 7bae3c35ae5229184a86c67fe08ba29ba01bdf7268b3a134721076e8efbe
15f8849b6b81d419edd4dc6b760ad2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 372867254b4044c7be47f310
ciphertext: 7d6359f73ef1c74ed6c1b6508305658a67051be22a26b3e09bcb301e5e7e
8ecbb4cc0fd72286b344937945824d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 372867254b4044c7be47f316
ciphertext: 0a5d480660e15025c956d4199646e3e9f57d0b2f5a81fc01830247291a5a
a36478c4ac001b52030361175a9475

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: cf35e1ec48699e2ac323bfcd6107fa64ead6173a9d657f2e1e13af3e5e5d0985
skEm: 8e48c59e05bbab3667c43a0efe6ce49a0e40858855f338df99ed590201ad89a8
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 4b3f3ac9dd3ede81975fa3d71388d3990fbbe2ce5d9e2b041401ceef9a146764
pkEm: 38736ac5c05fc98a630f03b458980afca2e3bf2c8dda840dd9db53bae6124066
enc: 38736ac5c05fc98a630f03b458980afca2e3bf2c8dda840dd9db53bae6124066
zz: 5c556648ac6108e85465b327817389ac510a0c570e4c3bb96dcca438dcc5fd4f
key_schedule_context: 00200001000301535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: bf8cc2fe58f6b5faa26c9325ee4b515543719990ccc1da54004448a5ad692023
key: d2868506d7a70c09d31ec897885018161ce28da656deb7f48c46fc75361347ae
nonce: 17e754b562978b21c167ec8b
exporterSecret:
4838eeb03577132f3ac3287ab16cf2b07c89eeb6e465113e8d4cd71e28ad0767
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 17e754b562978b21c167ec8b
ciphertext: 9b1f21db17e1913fd7142480375ef919da7e3dc1f0463b67ba1999f95401
2db041af1f32c5fe4214a09d194309

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 17e754b562978b21c167ec8a
ciphertext: 93ae96b2f982ca649efac72971965b77528dece621f66313235eae55e34c
841ebff5eb58afd818c1f4554aba9e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 17e754b562978b21c167ec89
ciphertext: 8f11c75a31af71dd98beb425fb64bd4d34c3b4f023e9a016e821ad29cfed
c60eb8a4a528cef3b55b684801fa9f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 17e754b562978b21c167ec8f
ciphertext: ab114ab1a539813915ec89b57c1a1325a5ba9db45dec8920206cdcfb8f09
eecf268e08ca0b7cd69b90a2954144

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 3a7bcd2c791fc1dc408b994644bc4e69d1504a29460d3765579fa3756484d930
skSm: 5ead55b81d6e8321de344bdf0aa39f0350487961c340c9a9dca30e9326690910
skEm: 4fe6bada210b9edcebd10b00ec3dccfbd80aa624e921460d8f546e819a90878e
pkRm: 24011582211e6f1f0b56dac8ddeca75473b474147149afdbb9fe80135639e46c
pkSm: 8fe55457eaa3e6fdaafecb77ca943f46a7829727b04eeccee57eafed4b25d461
pkEm: 703fe596482ab7b126e69a98da9fd1998c6d293b29865de706fb298d0e403527
enc: 703fe596482ab7b126e69a98da9fd1998c6d293b29865de706fb298d0e403527
zz: 15b4df17bc4545da939472049a63a50bd5b4ab1f03ae7cec269b2e28de009940
key_schedule_context: 002000010003025d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 1d6d506a0487e2648eeaf4cb4c35b94751be7cc14bc0789cbd162ee0b30b5c5f
key: f9deea841dc5a74f7b96d0a7aea8749dc139f262e5a39a9424eeb0ba3ab723e4
nonce: e0cd5e203563143011f18ba5
exporterSecret:
f0b51e720822062abfed6a591b1aa0a6b9d7cc88c6f204878ead07c736e8fd3a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e0cd5e203563143011f18ba5
ciphertext: 1435b2e276ff550398bcc910ce7d94f227da6972061c33743d42efea13da
f6f40914fefe6d9028010adf3714eb

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e0cd5e203563143011f18ba4
ciphertext: 783caed1152294e1c8b1fd9090c895f261c0c6669862380659eaa8dc3a0c
3b8fb46764a3b06d4f193b216081d9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e0cd5e203563143011f18ba7
ciphertext: 79dd78ee11500eacce6bc1cc2304b72f1e1264eb28b31e65f14bacfa76f4
91a359aaff0fafaa2b3f9881e5f67a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e0cd5e203563143011f18ba1
ciphertext: de545c964f9bc9b82ee97baa9cc7c3753ee7d1263aa10911d8d9d9e75065
e45b3b3ec2d044414198f0bd832385

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: b8e2fb05683daba0dbf85959511c21a1c3d322ae2ff511f62bc748e4309c9a7c
skSm: 398979f1a4cb83c18192de23a8b262909e91d28ab6ecf8d30e5457242ece0f0a
skEm: 7daad3a3c7b9c11cf5fa672e05e37e570ad159ec1021e8b9c2007a882dea3128
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: ed30873278100b1f5d88e282eea0b07e09178fde0a03b7b48e4598d765158342
pkSm: fb23b3b86d0429357013a6750aac9b8e53c56d53712441d1eba9533243f6905b
pkEm: 0f44ee661b9e731f6f6104745baf506d0f884298741613aa8c5a60f169f1de62
enc: 0f44ee661b9e731f6f6104745baf506d0f884298741613aa8c5a60f169f1de62
zz: 3a340745606d6c0582954283f02a859dc684ca6e5d52092ca7669a11b202257c
key_schedule_context: 00200001000303535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: e2c69de5a959da185bc7450e4cc17720154709a4031ce8dd5f28a825e8288788
key: f4c40f32ef091c3d7667b476f3e333c33892ca342dc639fe5d2e724f0f97e9aa
nonce: aaf8cf7f968288fb8346923b
exporterSecret:
72cc97297267d26f43dc179af9e1c043e70eddd67fb98893d23b68f2b4297d77
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: aaf8cf7f968288fb8346923b
ciphertext: aca9df0fb92deee7a2e15bf09dfb4e2c5d4c0378aae0be3990be84ae98a8
c989c4279141e16c3e87107b844998

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: aaf8cf7f968288fb8346923a
ciphertext: 184ce6f508881e07d6bc43057743d94ac5b79cb358b761cc435e89583289
7a940cbb6d8295e3e9fb85deba5c44

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: aaf8cf7f968288fb83469239
ciphertext: 13ace3314f124ca66e118fd5205ffa04096ef8525d63e58cdff9aa6d75d0
5ad6d1f9be3e5e99ab6adcb7bf5bf9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: aaf8cf7f968288fb8346923f
ciphertext: 018da48d130fa227097379cd6252b51533617d56d2c7fff6035952b29972
5f859dc15c44dd9cce3914ee3786e0

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 05eef02dccecf8d642769aa83b2a13bcc96c43beaf80dc59ebaee29e6f7c3c51
skEm: 36dd14fc4351c521ae5cb09b2574c49e33da47fe00078b827022011ba8d3c067
pkRm: 049ce5df3b9e46ce95b46552d2b0100aecccb1200334206d6602ee8e9398974e1e
359606fde1f208c09e79e25776cd09692958795e1936ec373c67eb8a89048054
pkEm: 04539ff924d6315cfe724c470131eaf6e06044c25da5143604f70849ff978790d2
646787bfa196529e5f7e62e170b72abd4b8f6fac1453cc557bed06b9a196e554
enc: 04539ff924d6315cfe724c470131eaf6e06044c25da5143604f70849ff978790d26
46787bfa196529e5f7e62e170b72abd4b8f6fac1453cc557bed06b9a196e554
zz: f7a3673cc46cae7b68a076c57161d0df0594202624d51423d1375fe2c32b3af3
key_schedule_context: 001000010001005d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: d47b535abb0c634ccef6bed24a8692cf30a319ada1f8177004c8f784ae504abe
key: 9da43da8323610e8856708219c8c2de4
nonce: 5a94aa57e8e9252f6b7f2ffc
exporterSecret:
f1ced4d62e7999757df8c477e4e96a73858f7a2c21c5726915b761a0631f49c3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5a94aa57e8e9252f6b7f2ffc
ciphertext: 3eaa3d649c4d367d8055cee9187d792f7c1a406dc10ff4e3168c75df786e
84ff3a3adfda43c8a697a5aeefe683

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5a94aa57e8e9252f6b7f2ffd
ciphertext: 7f99438ff269970cf3efa326e58cfff63d879f4af66502ff8f4cd5d92606
b7d960d1ab4a6a4a6c955b4251b20b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5a94aa57e8e9252f6b7f2ffe
ciphertext: c3a0475fe561b59c3c15be5d34ada396da329c502544a1f84b637ca35aa4
2d07908be5c351340747cc0cade1f0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5a94aa57e8e9252f6b7f2ff8
ciphertext: 4d4ab5772920d8b88c14b7179c43117eb9db6a08dd1f37c2f83e2bb721bf
0f56a8ffcab1d8f9ab85b62db25697

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 57c8d727add7c7f860bd9d96040f23ad0969964eb8d5775a928f7af4ab39a5cd
skEm: a32ef2cad2702ea38fdacb7e5f4d9f246d84443083806e15b39727bb0a7c39e6
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 04a133a223f395368c21c4e1e2c4abde0b4df1cd4c854b4102c8b6128b788666aa
c6b08b22dc244cc90983f0e11f86eb532f6d74db2ebafae90e7453ba22fc1b37
pkEm: 04c7196429577922ca376599180085e9a38352dd65d0526886b6edb8af006bc48a
8b51e54e36e792bc7a62a3ff2518283e4249f784849b7ea94059c5483e5b96ff
enc: 04c7196429577922ca376599180085e9a38352dd65d0526886b6edb8af006bc48a8
b51e54e36e792bc7a62a3ff2518283e4249f784849b7ea94059c5483e5b96ff
zz: 7d9a5aa22039b70964e88f372a59f6a35536e8cfee211f8f28c840aacbd623a6
key_schedule_context: 00100001000101535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 4c1a6c985426b0bb06cc73502ab23550fa0633efe6ced913be6c931424866160
key: f365361d889cbac9b0407b71d2ede124
nonce: 85c00c894de00f4190994643
exporterSecret:
1ee7214a901a875a12142726eb6ac108651a87c7639b566f741174b66fd4127e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 85c00c894de00f4190994643
ciphertext: f24351682f21c9e44cf7401000bd074f6ecc2cc2022599d05e1908bbe8ab
c51645e9f988aa7d5efccc9095ad57

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 85c00c894de00f4190994642
ciphertext: 02e9e0f83abcdef6d6b58adfe94a47ebe3485c2da7475b3da6308e0eae65
19259282311b6b44bbefcbd7726cf6

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 85c00c894de00f4190994641
ciphertext: 52fc6230dd2425034ccb8fb641b077a6778ebf67c57475ef94094d859191
a039b4a56571a2c23c179f947147ac

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 85c00c894de00f4190994647
ciphertext: 3645a42b7d47ca32deb47beceb20d89244b72863afdb1bef5c87500a74da
59f0be2d7be178aebd8d0b84b1aa35

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 2ac44a1638b9a96e1c0a6b8aa42fa075b87c4daac1accbe48dfff3a90be75df6
skSm: e9567170afabeea965fd5b2ee2f8451647afcc8873977456b78bca4fcb3cfe82
skEm: 2cc766e6dfc30b45de6619b9ecb83bec98ab76dc5ae326ef63499879d8add7ee
pkRm: 04849ebc2f6fc7e9c95a68cc9923e9ce84e4a8e831384a7ef6e7c66b4c4d2b1a8e
3421550d63a38548e513468bb1f55f271f4502195bec85c7464728e6f41a7baa
pkSm: 04712329a3189683aa7070ac133cc77f6f06eaf222679ef19699e1e5f1f0813b2c
84625bdaab4a36d1c92e1ebc22136169c1e2b6bc7eddce302f9ca4051217a511
pkEm: 043492350d6b37c9cccf7046321a377b23f9be5bfc20912e5cacd0a47ef2ca068c
df4547647de44f1d63cab58c4025403b6ef763c1554ed8f5f57c164e328e2c5c
enc: 043492350d6b37c9cccf7046321a377b23f9be5bfc20912e5cacd0a47ef2ca068cd
f4547647de44f1d63cab58c4025403b6ef763c1554ed8f5f57c164e328e2c5c
zz: fc9b6d0cddbd7df13a8f25b17cdd9a9a1abb414c372a68094dc6dec64acf5f1e
key_schedule_context: 001000010001025d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: dddcb48b09a137091957d777c5d671ee7abd165964b7eb7c5931b0ba61aeaa33
key: d97185020399ddee42df6971046dfbfe
nonce: c054a5794540af1aa4a19638
exporterSecret:
5ebb0d9ae2e58b1bb31a70f79d08d2b3b0eedb79fc33f3518bee32ca86dfbe64
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c054a5794540af1aa4a19638
ciphertext: 31e7254aa10627a5dc52722ebbdc62d782b0bcbcaab1d6de3967c79d175b
6408f83a110badcdb4978ebadb80cc

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c054a5794540af1aa4a19639
ciphertext: 8f33fc8ae9b38f6ec5ddff8bffc7e32bf53e43cd704a96f8dd1dec1ba868
8012666015dd388bda34a2844fbb35

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c054a5794540af1aa4a1963a
ciphertext: 1fdc64ef305d2963218d911e1e7f21f842bfa5816cfae65d579a9c65badd
466e62c50e80cfdb84bed2a9fe11c9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c054a5794540af1aa4a1963c
ciphertext: e8e43c45b07fab3ef827f94cfb27218491fbe0b5584932e4bf9ee448c5e9
ebd07e3f25b475f747ed1fcd3626c4

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skRm: cfce19a179e066169b3fe4907b1afea1bf9ad78647992de4fc6677417340499e
skSm: 98d722ae00fd5541f2be8285c7d0628c8d1e1700e4da229da8c475ac994bea84
skEm: da1751584f1c58ed3a15955e71521c6cb150bc3d28419b23206be8a5aaf6e516
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 04c356c2c94f307233a405fd635026d4508c46d8e392560287472cea376aca43cf
0b71ff3df31ad7eac87e1f3bca19c0c6a3c24bacb4e414748f61949c9e58f677
pkSm: 04933e9cf7c8c0b2ff4480c7499e3fefcf602d8019c922f63e7fd9e2db459d21ff
611dd10bb515750e423c84ae7a6f6e76c346f84112950a8ec52f983e920b87bc
pkEm: 04e034da35c3e3046c101a1d131dc3c07f8fef04cc120abcd88add16fcadd63fb4
e5bca0b80fb93886366891ab0ec0d7dff9fcda7d507a4b35c50bb6339ddc1f12
enc: 04e034da35c3e3046c101a1d131dc3c07f8fef04cc120abcd88add16fcadd63fb4e
5bca0b80fb93886366891ab0ec0d7dff9fcda7d507a4b35c50bb6339ddc1f12
zz: 39fd1022163aa6391fffff0c5e331c5b866abefc41c8d003e19e9aea66096abb
key_schedule_context: 00100001000103535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: f8944db967989d5bb988cd443ffe84ed06d18f6e16d72c22f75b079b5bae8a96
key: 5efd9c50950d6be290b41bb8828d6d89
nonce: 3698207e6d118c6369e26f74
exporterSecret:
7ead73ef52161dd729f5f04dac32c69d887f1f2d82fe3a6f1dc76df58fc0014a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3698207e6d118c6369e26f74
ciphertext: b96934ebb9849d0c25d750bc2066ead24a9a60858b1774d01ee4d599688e
250779283579907dccac31d44a4048

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3698207e6d118c6369e26f75
ciphertext: fca03b268cb768d98a343861cc82841301742bcbbc4812646f4f1f84df59
ea9d5e856a0edc910596cc855a1db7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3698207e6d118c6369e26f76
ciphertext: 8612a263d4c80fb0d9287ec01891eefe61782026fd82cfffa4cddc0302e3
dec8ab6103a7e0c2602431976a8f29

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3698207e6d118c6369e26f70
ciphertext: 13a574a2b5152748977ba7802e64e3548e3f87020af188b62479915d4ab6
3ae201ab18a0b834732a45ec680409

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: dc305ba2d1d92f55dea304b35e83489df2ae1ea9b685aeb0b2aaa67ff67890c1
skEm: 80f5e611f760ba7765467ade0a1ad5d80a424614161d29c38ba80fe21622d462
pkRm: 047c2e345c1cdcb0a9687ad458628787c87f7f1b7426526e155bdb46908e355011
1847a45b5ba1ae5b69758c7b0980587cfba7e58efca5da62cd1700064323337d
pkEm: 047fe4b0f8f3019b10d53aaf04a58652c906779be4c59aa944decb5ef6610b74f3
22083645a8eb2bcf9d1e77731d8758abd0b8cb057610d5daa9a2674f3ad50a4d
enc: 047fe4b0f8f3019b10d53aaf04a58652c906779be4c59aa944decb5ef6610b74f32
2083645a8eb2bcf9d1e77731d8758abd0b8cb057610d5daa9a2674f3ad50a4d
zz: 713a150d402fcfbc3cf1ab22b286b711fb9a5300f73390e2e69498fdfba0bc11
key_schedule_context: 001000010003005d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 51274351f31e7238b6d2e7df11173b30db82bf4d1bcba24e3f6c990f3727c11f
key: 3271dbf2eb5642ba1c6fe3b6b865a6664dbe251bde04790d598771ce606fcdfd
nonce: 130169feea85d66f1860f9d4
exporterSecret:
1b4b266331ea8ff3705e393c2fb00c056d942533f6ffa035f13cba653705dabe
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 130169feea85d66f1860f9d4
ciphertext: 5a99248972a831e47695180471d6d225283ba237549d1fc36cb86f12b1c9
eeb93b2596f32714c57c0b38aab56a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 130169feea85d66f1860f9d5
ciphertext: b836e13a009fa9a7cc3aea41315c39df726ba7472e90a0ed444762f4580e
c54639f465eaa05a6a6e59708e5527

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 130169feea85d66f1860f9d6
ciphertext: e960bfba2eae931f8f01d67f3de70c2f0456127fa96fd5035b0fc1201190
077d4b66975cb98899ccb5f9d839f0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 130169feea85d66f1860f9d0
ciphertext: 21dab5f61e5173e1fea448b8c86a6dc509e4ddf78b08fe2a69c369876b8a
d21e0fd20680c9ab69816af3383526

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 52f526ed1911a2e09e771b77eaac64bc63f7ffa929a0b4a12d751ed0b85ffcb2
skEm: 255fc1a533127217da1e1a7851432edb69fdb7e1983c283d0869c8f6f7513d4c
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 04fb0d7d637b5e626a8a1c8b6c92fd831c9f52f4499686d3b16ecec39336b89e65
987ae108efae23547ee115092281d888aef3f1783cc3ff186413bcb794be837e
pkEm: 04f13691e552496b762a512edc320341a7b090b13fb86f3bd09093ab998bc79d92
4e28cf5d578d0929b18057cc30cafdf08bb894c0de0e2b1aab862b5ab0120af7
enc: 04f13691e552496b762a512edc320341a7b090b13fb86f3bd09093ab998bc79d924
e28cf5d578d0929b18057cc30cafdf08bb894c0de0e2b1aab862b5ab0120af7
zz: b2d15e6c796800b651017acb72a4998b8687a3adf80c4aeaa24ae9571ff472df
key_schedule_context: 00100001000301535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 96b3aebc9a70ac07fe7169bc512fd1b9a5786599b30b9a300fdbf62722d55b8a
key: 1cba95d21899bb3711b22d099dd95ca90b3e253ac62d64b9e6119539cbfa0bf0
nonce: 840123fe89869e58c657b5e1
exporterSecret:
e210de0ec5ab08d786ce6387f4a058d51bb1374a3e8e2d96db1857bb5c142678
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 840123fe89869e58c657b5e1
ciphertext: 460f8e37d7583a9fc6342cff5a70109b08fcd97deec0d45f3b5e28752afa
a404025a3a1ab71bd16e7376ac38f3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 840123fe89869e58c657b5e0
ciphertext: b97cf3a98da19294bf2cb4a12a2f55548843c511c4669ed1f391e27da2ac
20cdb62c5d8d67a53b6c0394f8a70d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 840123fe89869e58c657b5e3
ciphertext: 8b62f74208c87be7e015af435469789646a7bd3b14648cfe5dc419507294
9696429b154b304c491a7fde78fd23

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 840123fe89869e58c657b5e5
ciphertext: ecdc26c017fcefb85e8f91ca8c04400359837629abd02954544130da34fd
e7eb657606a140a8b9e3d20a1bee7d

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 69d9d5cc403dae32d6d5290eb7f8ce6468707471c742ef6431032bb1b5c06db3
skSm: ab63381f7462f58440d18e7b56a64391c7dff45cf30e53d6380446683df20ff7
skEm: 5399ab9dd0df607b59f568ff32d1679158c9d9e61153792a0ff9915c41d076d2
pkRm: 04b8df801c99a14fc6398a4ff4a029f3089978136e0c721e1eb857e0c63f43f74b
597b229d0dbce2726c7609875969c0f51dfa27fe0fcd03976001e4dc1068031e
pkSm: 04d4b6c6ba86c0e09f3cbbf722078d393d3b876d79693794bb7f3380cbab05093f
cbfe85ddde3736087e3dda84bb162c32b4612adb03c601c65e096518c8cb834b
pkEm: 04e108c95782e1c6e3c645ef1db8a51dada60fcb3e3050a18847610e289f2a1626
72e83f063b85f7e4df47b0bba76203d67589d7a444433ad1adcd196b9b1d9aee
enc: 04e108c95782e1c6e3c645ef1db8a51dada60fcb3e3050a18847610e289f2a16267
2e83f063b85f7e4df47b0bba76203d67589d7a444433ad1adcd196b9b1d9aee
zz: 64c0be49ac081229078e1389d05bf24bca5a81ce553e0dd16c7a3eb0bd3e70c2
key_schedule_context: 001000010003025d0f5548cb13d7eba5320ae0e21b1ee274aa
c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: deefbfc45ea67582e619f58a795f812f12fc0050b1db0c44c53d24901d32f4e8
key: 1e93fbf7c38cb958fa888c06a34e2b108427ecaa53b3aeb3635ba7128aeacd36
nonce: c8977256edcdb9b7623a24cf
exporterSecret:
eb3a73c7313c98262291768a5576513e6e1d8fe364c6f0ef19fffd4389364748
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c8977256edcdb9b7623a24cf
ciphertext: 3a102e9949c2e77981528ed40c7578c98d96cf51eea8858fae3447b2bc47
14bb1fb961f5b1022aadd7af5e1ff6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c8977256edcdb9b7623a24ce
ciphertext: 32020d5f7f4b2bff4e7fa2da9fcb077053cb334bd4b6e5cf4eac9e6694e5
792a518f1a1ee48f5cb943ffd52507

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c8977256edcdb9b7623a24cd
ciphertext: 88e458df2c9cdaeea41b55f3ac834979fb60fb5cec79031babd4f684aa16
546f573a4896587212d5eeb64eaea9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c8977256edcdb9b7623a24cb
ciphertext: ccf2902045d481ae33118bd76a104496721e7e0ae287e5671acb621964d5
763b04bc5ee9eba295566ac2348e39

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skRm: e8c36b7e3dbffcf1c190187d77b6206e08dd266706987ef113edc8147172901c
skSm: ee694935e25d5571581de6028a8b4b3eccecd868504fe359b7acd7c094996350
skEm: 074e51bf9a8443bc96321e394fff94b0355f9a4fab332cb8bc32e7066e29a4a1
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 048780283a075e52a8799dc787ef07ea42d056ea2e33f7bacf58a151bc79b4380d
b6634f360a1309a9dab49d29e0b0ce7d4efda888aa19ea49d6de7532370b786a
pkSm: 04b2fb1801e525f0ce94a16e7f8d556cff27b8e22d1f28cbdf5a07c8f7042914fe
c6d57e901a2d36c35cdb76ce688f27c03be6970439ff7632183543d701dd2415
pkEm: 04a934438905c94f235b8f20cdf3d7594cd9210112873b501c47ac7140cb83e952
f52288234e5038744a3323685888557fd1114d643894c69a41c3951cf569f087
enc: 04a934438905c94f235b8f20cdf3d7594cd9210112873b501c47ac7140cb83e952f
52288234e5038744a3323685888557fd1114d643894c69a41c3951cf569f087
zz: 63609430872faffd186c7110be48afae5a8a144f2712227dfb67dfcd60e900e5
key_schedule_context: 00100001000303535aff74a3119261af116227072152ed4bb4
de6308609d770601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0
c49f16cd56fc524af4ce
secret: 60d131e6f85544d82a788455f48296fc7ec6a0e1b300cc93b3610921b81a9c23
key: 67bd8c63cff5c51b55244019f74670e8bae8dc0deca3939ff108b1e8cea0a7d3
nonce: 46ee46800378f64f70e5acb2
exporterSecret:
1e7461f48e690d75fee3a1d967c4a427e35f05c4ee1b928d0d63dc31b74e687c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 46ee46800378f64f70e5acb2
ciphertext: dc2af05ea3536d69757999be1ef65ef57875ae62907b9eb51970adb66b48
ae5231e66da043dc513f67c6f6dda9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 46ee46800378f64f70e5acb3
ciphertext: 29e5cafaa410184a1793865e6ff632c9c5d816cfa56a3e10548bcb44d647
cd76ebbd81876326df90db8942d5f7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 46ee46800378f64f70e5acb0
ciphertext: efc8b382e3d1282d064076489e900220ea0c85a2cb8ee60de084ac64a9c4
d50d1dc8cfa4749404b5a04bce338d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 46ee46800378f64f70e5acb6
ciphertext: 707c39b3d234e996da60b7f5f63588680ce76cddb7ed94bc2fc79bf660a2
1cd72931717cb7ad7453ca6362dc16

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 01723ce49eedaef6f15bd21c8623463d83ba51fb208dffe32922f84b44cb3ce637
147cb7dfa49026e095a57fae660c35ebecf706f20e05200ce276fb77db3e1f5b8e
skEm: 01f2ed36c8324570696033b91d2c784fc8a8f6f8bfc324e8a6098dbd3cf02d8633
1b2f87ee6ce2871d9a91bc5d0b6122d70602be1eb37abce92ef35ef062942cd4e9
pkRm: 04007e5d03188c6b0f663a236c030e1846445792b13b49b0a5d035f1311d82ae59
e2bab498f55234b1e5ecab13a7dcd20fbb0116e170525721bd6cf27b70733daea5d000ab
9215d0baf9fba4614505bb70c5b54c4875028eb7ee7a7d2d09896055ebd1d437e7aae654
0eeb33dbf0865c5207cc1570bd94da187856d7ec86ffa67789a0226d
pkEm: 0401be0edba930e8c1636bf4e62afb03535ca930960e9819daf3cd065ad0467ea6
5952ea5083bf180703e0fed25bd860bf591b89e15999826e843d34dff5d2d1d4be5201c9
a98d7dfd896da39ec394379f1d6c2d17f20a3bad1ed3e683958c7fee454431eaa39f2d39
487c2c5ae069d6865412c1e8f5cb55affcd2bec4b99d082419448750
enc: 0401be0edba930e8c1636bf4e62afb03535ca930960e9819daf3cd065ad0467ea65
952ea5083bf180703e0fed25bd860bf591b89e15999826e843d34dff5d2d1d4be5201c9a
98d7dfd896da39ec394379f1d6c2d17f20a3bad1ed3e683958c7fee454431eaa39f2d394
87c2c5ae069d6865412c1e8f5cb55affcd2bec4b99d082419448750
zz: 4dd2859e68ada495d6cf42e1fa1c64bfd9daad423acb2b8a7a8fbed81679a5a45ca5
3d7c9997d58d2794c56ad2f181279487dd1e1c3b12860adea789656d2292
key_schedule_context: 001200030002008ca13b5d680259cfa265de13dd24f257083c
9403c01a8aa3320b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd87
1711e356ed9bf5f1e0d0c70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1f
f32414767a12c08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088
177c
secret: b25735843dddc404259a29890918d1879d6f30a2ae3975bfae504fe705afc5ba
d523a56ce272c7e2c78dafc9a8827525289ad1a7c4b3909dfd6bde508825a53b
key: 0dddfa512b9f3faa56dbbe7382c9bf6a39d6c4b66c178195e8b606a23175d964
nonce: aa0ade11c5f13f737e7a7639
exporterSecret: 29c080800c0b60d8dd7a769c18f9e79028ae665c0d2874822c29365d
25a6eff18236c15692e534e24a22029a66b2e5245bbd27de65f07b5f399679d315450f80
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: aa0ade11c5f13f737e7a7639
ciphertext: 8f22ca0c8c497ea7cacf6200e137cb8bb8677d76d3d9020a4008d1f9d42d
e56039388d5d5dade52f8aebfc5b8c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: aa0ade11c5f13f737e7a7638
ciphertext: 1a44ae17740b56eb8d41ff70396d1f504825401db59117edca6a112f9722
52d04e898456adacd77a3997e643d0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: aa0ade11c5f13f737e7a763b
ciphertext: 2d83b69b62a62009acdf0fe88be077e2395f189091f052958f5b2953a228
05a14bb009434455e6112e25118179

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: aa0ade11c5f13f737e7a763d
ciphertext: e658cc2d87ef46b093b6d47efdbb502d98d1a8728087d5090ce67e281585
d5655a8f8782f003d3e8c9892b0289

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 018bd93afd69061f25ac1f97dbd941c439795fe0f345ecfecaddff398dd34eef8f
779e0a505802ec59c0621b089a511e23b45123c65659d95cbb0804f7038334cb77
skEm: 00d07bf45e3981ebd73adae0e913d273af70e040bd086c9a551a16a4e07aad89bd
d2ccf1bb9ee89e7dcee0851d4ced282e11298f031059b520c12593766f443878b2
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 0400f3bebf1f1ef6156e0f0f8475c20e822b13eec7506e6f2afd1e4a8d47a417f4
c60b29e5a6fcfc35f88a30b6610f8bf55b4a59ce22111952757deaf450038001121b00cb
bef36a4875f40672a8cafc043b7951e57a2ee61a5efd9e9b294959363b537e1017000579
0e3e7f973a53cda9527a9bc121badc8ca389c4cb365404d2ea4e8dee
pkEm: 040145645a95e149fa2a52fca93097c9861dd51cd1ab26f85c6ef30189bdf6b804
e812e57c1d3177e14e38a5ac601cc2b6fd65958a66c8b580c1fea54dfe21379b0c080014
02de4a553fb8e3b741a923ab278791822d90ad09c186889afa4fa3d18fd3ed4c5a74099d
388fc49f8c43be2a6d30c559ef447779cfc1b59d773991a9dd84b83b
enc: 040145645a95e149fa2a52fca93097c9861dd51cd1ab26f85c6ef30189bdf6b804e
812e57c1d3177e14e38a5ac601cc2b6fd65958a66c8b580c1fea54dfe21379b0c0800140
2de4a553fb8e3b741a923ab278791822d90ad09c186889afa4fa3d18fd3ed4c5a74099d3
88fc49f8c43be2a6d30c559ef447779cfc1b59d773991a9dd84b83b
zz: d16b10238bed02c9bc4d2ed12af6334e5549f971d91d1f4af5a937bf871e920493b9
c6dec2cf7f354ee1c51f50b47ce4d85d00908f0a87d2df644eeb1b2830f2
key_schedule_context: 0012000300020119d7c2d36b1355543d8247391c51c3779291
51509971ce1c3cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6
f306e8d335154d673d8dc70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1f
f32414767a12c08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088
177c
secret: b6f580d136ce48b42bb265c8402db6d6a8713bee941a0405eb22af273049a577
a48b085d6eb6b38c571887bc48625e2d35387f8d5471e807e4a0da80cbb49ce4
key: c60f3b74b445ed930ce35b23ea60da0940000bf015faad25cbe5cad1a93db476
nonce: f1afe152468bc3c28c0e44a2
exporterSecret: 08dbcefd4fa95b3436713871caf1f44ebe8dd3d1aa13d16155d5d037
169dc39fb2314a7d0edb2c7b5574b1c4fc1b1c84212b05bbadecc6842fefd1d3605e6303
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f1afe152468bc3c28c0e44a2
ciphertext: 9bc8a145d2a995937ac599a9f699056f5b27e1e7bdae253ab7a52b389938
b83599521461913d6a1bddf7cb1ff2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f1afe152468bc3c28c0e44a3
ciphertext: 392e3a17d05240d379ce90dba50e4f382284e041235cfbdd6a5376adb704
5fb95d6284b985280ded1c22c75930

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f1afe152468bc3c28c0e44a0
ciphertext: 2b75dab7c688cb0e635eb57fb830892c8c72799a3325cd8bd47bc95ad2e1
822b8740fa36aa56af7a04b28640f0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f1afe152468bc3c28c0e44a6
ciphertext: 87dedfd43b36358a388c330b206f79971261d593ea831b423a189b3106c7
7955985ea270c9ab5508855eced240

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 01e92224219f8e54f708e0e16f7b7565536d50f48ef934498d961e6eab01a7c5cd
ae9450249f5e63e8aa942f547fb6f09253b5057294b4f6ee3ed86aabb13d8d9c18
skSm: 01608b025b6748c90151f7a291fb185e9fac7bd98b7695cb00728512c17b2996de
d63a2d00e9d0fc27a9988d8fc307d6b13d8832097f19911703d17e76f044c6857e
skEm: 00f8290b8153905ca9c483315cffa02cbdd6935e0b608e18dd667ec1375983922b
305c1c33e404454ffbc2c63ea06213ac03340996d96865c46b5dfcbc61e8819191
pkRm: 0401294874bd19367f494922ed536ab4a2cf17cc71c403cab9ce763906bcec5445
cd1fe8c8b1002b7da2f3cbe0c0e894b60f4169e121d0a714dbde7bb08a7d4dc440d100ae
f7af040f653aed85b9137c1d4a836f6773e6bac4a607f626c57cc0e6f2c9c960fa1cc3a0
4db2a8548d887337f1494396bf73102e7871c388ffd53ff6c227a35d
pkSm: 0400395c7b68bde87e774e5b6d73367f35693f16c8c5132f32900845e2373fce3c
26bc49032c9bb1df39b2e3aa3517056bab199234543cff38437220e6a5c4efa13e4500dc
050938bf0329d48431158a7ec046e72ef0523c130b689e1ca178cd0f0dc794a69ac3c508
153771eca0e443b538bbeef9754e86cd2c68159adf8cd9f2ab28597f
pkEm: 040024243ab3f6226d85ab9516846191e1b07c167357dc61c4ef49c53222e372c7
f1e12bf8d7a0cb4fef812b0e5a60c27ddf53ff2220d0a710bd9bb21767c20e3e7ddb012b
6459010d94121e76a6e642f76d30873671bdc4f87f03f6bbdf11c01fc81fae54b8314cb0
dcb00608e4ffcff5c5f3cbc78815520249a190ba391fde73f8731e60
enc: 040024243ab3f6226d85ab9516846191e1b07c167357dc61c4ef49c53222e372c7f
1e12bf8d7a0cb4fef812b0e5a60c27ddf53ff2220d0a710bd9bb21767c20e3e7ddb012b6
459010d94121e76a6e642f76d30873671bdc4f87f03f6bbdf11c01fc81fae54b8314cb0d
cb00608e4ffcff5c5f3cbc78815520249a190ba391fde73f8731e60
zz: 14dad90eaf4c433b90ae24a8ce09290d3dc410e79f70a7e7546526061a8f8020a235
f002183b3b56db9828defac381c0e883e7f159cec9e0205fdcf6542aefb3
key_schedule_context: 001200030002028ca13b5d680259cfa265de13dd24f257083c
9403c01a8aa3320b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd87
1711e356ed9bf5f1e0d0c70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1f
f32414767a12c08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088
177c
secret: 0f22ca45b09de23798aed55c32bb6ca2d86a8630ad1d7c0e0f4766db4bc71317
e094bc030b4630d32675806ea050be87680263da61b1467c87f316764819a7d8
key: 0a2ff26537bda8015e73d97c7561caeff5f31cacb8aa625a0fe13b436fa2059f
nonce: 9c23084786d19281fd611e6d
exporterSecret: aa953aff14d2d1ec50098d20b798ac76fad7a536e6d19a63df0cdf6d
7aa0d30eba876d0c9551c3401387344bf716a9927cb1ee7c5515c55bfb45b47926b9b51a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9c23084786d19281fd611e6d
ciphertext: edbbf3aaa09b0cba812c7d5246400d2d676dddf205eff9a047aaaf6d22ec
6f959e0ecb33ff4277702f796d4aa4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9c23084786d19281fd611e6c
ciphertext: 0b6011f3258d0335481bf0d71105d6be1b0253e21434254ab165c8656232
a95c37cf0e42de1ec16877f80ecff7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9c23084786d19281fd611e6f
ciphertext: 1b6d6ae78a6bcec89bfd573290c6bb21eac7e8c891f43ddbadedd1992fc0
10327e8637bffa12ba5bcc8b44973f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9c23084786d19281fd611e69
ciphertext: c50b45531d14bad8b30ca566d8c962cf4557333c5fa550b13b997139d96c
c76723208783961280da3ae632cb73

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skRm: 00ea9d6592fb9d9ef09995d6ffbbcee3c594f04d19968260c9ab1c19e6ee48fbca
dacf29c0f6e8dedbc36d1b6f852a75862cee8d6e6efa9a3cb2d60ed6ac4b804701
skSm: 01f73f06d850c20a682d00f5c0df4c35acd689920629dad9cb9a2457a9e71fb07b
813d94f4d0b7a83701ca4d17e222393fb439cae31c9eb1d36dd51d388a1d8a5a11
skEm: 00c6d6a2a1178033893a316f80b2c65a6813b306188cbaa813783fea682f6385df
c2c60ab092a9386047eea710a9deb9d759c998d940514d0090fbc166abca38c93d
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkRm: 04014b1362c6df77d0467484b2b6c7d21e4e1478877fb7e0d8ca52614e4effbefc
8be8159d19a41871467532227fd3c730e53914d5475f7ee2c95b7f9bd7f6f3dce5aa0071
5c2bec7c684212b26d22dbd40737c004387de596b655e80d101c4096668624d38cdfb1c7
5ff73b890075bb871e19975505f2c7cfe5a2d2f2f6ba0bb9425e6bfd
pkSm: 0401fc2a46cd014d2a11f654189fb7004a08f119e6b93bc67eaae7153bdbfb2834
2c9fed4a20996fee7d336bfe638c57d3b0b862a265bbc3ea1e57f6448e438b69ecc40074
2f2b242186d835f11f68b5b0d97676d1bfe9958fe5c72e8fc0bd8c221144163fc8f917f2
aea44c791acb7afb8ae663f3517b08b7cd1d4dd83aa827e4158565ee
pkEm: 04013809c38ef454f119b82c3499f04eced0b5bfde1eaedeca7d4fd881aad575c4
3a1b05f337cefe3df631e30cd1f4eb3976d663a5379fa8093a2c4253e3bd17e5efea0182
6a42bebeca87ed35619e3f3f102cc4c2a9c69297316dad9b44b21e784a6b45db8ffab148
3215747e49f994135b430c96c28b3ec87820e361c699ac935e626b68
enc: 04013809c38ef454f119b82c3499f04eced0b5bfde1eaedeca7d4fd881aad575c43
a1b05f337cefe3df631e30cd1f4eb3976d663a5379fa8093a2c4253e3bd17e5efea01826
a42bebeca87ed35619e3f3f102cc4c2a9c69297316dad9b44b21e784a6b45db8ffab1483
215747e49f994135b430c96c28b3ec87820e361c699ac935e626b68
zz: e6b49b32180c59105554f8bb2fd628094c1bb2b97472cb2dc3690680f78689266e5f
af40e756488e0204c9e0ccae8b18363b5820682c47423d12a61c18c24586
key_schedule_context: 0012000300020319d7c2d36b1355543d8247391c51c3779291
51509971ce1c3cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6
f306e8d335154d673d8dc70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1f
f32414767a12c08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088
177c
secret: 188b2b94fad131e46b4caa9e876f15e0df350193321f36cd39b51763ffc09af2
d63d34b5d32f58577f7bc669cfbdc751a959e728b6db3a4213d91e57fac03aad
key: 1ba5aacbf6e5747f068bcfd6cd5e2523c37b172e5edf1649a815f46c02b5109f
nonce: 897750eb7c843a54dc2bf201
exporterSecret: 59fa50bda199e0f5104f8be9dbf8c4a628b53a453d0bbd9ef3df6660
d8d2470117f5f70c41256d5a30bca82a2f6767babfe4e74925b24374fcdb74f184b24c7c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 897750eb7c843a54dc2bf201
ciphertext: d97aed998883adb5f470f0b62889542eef7550c8e633bd03450e5e6641de
87aed21071eb2d9d88473516150fa1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 897750eb7c843a54dc2bf200
ciphertext: de73bbb467f5f722204dd43186d9e07dc05f3b142f83e4102d1889b983bb
3c390e0f86d735d7e7c46bfc86c9b2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 897750eb7c843a54dc2bf203
ciphertext: 817d0fd59908898c0235d2e4caef2476c0b1d822599a698d9d6cfdd14913
cf3c39c53c13891b03e119d2914f94

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 897750eb7c843a54dc2bf205
ciphertext: e7493e82e62ac07df46c2bfd0cd82029afb6a461fd987be31c7336924a50
001ec32d75fe089fe300052c3c1b86

~~~
