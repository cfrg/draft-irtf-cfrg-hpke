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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/4f8665618fbfcf3a4135bec2f3de5a80e7f57489/test-vectors.json
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
  - Marshal(pk): Produce a fixed-length byte string encoding the
    public key `pk`
  - Unmarshal(enc): Parse a fixed-length byte string to recover a
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
  - Nzz: The length in bytes of a shared secret produced by this KEM
  - Nenc: The length in bytes of an encapsulated key produced by this KEM
  - Npk: The length in bytes of an encoded public key for this KEM

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
- Marshal(pk): Produce a byte string of length Npk
  encoding the public key `pk`
- Unmarshal(enc): Parse a byte string of length Npk to recover a
  public key
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
  return zz, enc

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
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
  return zz, enc
~~~

The KDF used in DHKEM can be equal to or different from the KDF used
in the remainder of HPKE, depending on the chosen variant.
Implementations MUST make sure to use the constants (Nh) and function
calls (LabeledExtract, LabeledExpand) of the appropriate KDF when
implementing DHKEM. See {{kdf-choice}} for a comment on the choice of
a KDF for the remainder of HPKE, and {{domain-separation}} for the
rationale of the labels.

For the variants of DHKEM defined in this document, Ndh is equal to Npk,
and the output length of the KDF's Extract function is Nzz bytes.

The GenerateKeyPair, Marshal, and Unmarshal functions are the same
as for the underlying DH group.  The Marshal functions for the
curves referenced in {#ciphersuites} are as follows:

* P-256: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 32-byte big-endian integers
* P-384: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 48-byte big-endian integers
* P-521: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 66-byte big-endian integers
* Curve25519: The standard 32-byte representation of the public key
* Curve448: The standard 56-byte representation of the public key

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

  psk = LabeledExtract(zero(Nh), "psk_hash", psk)

  secret = LabeledExtract(psk, "zz", zz)
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

| Value  | KEM                            | Nzz  | Nenc | Npk | Reference                    |
|:-------|:-------------------------------|:-----|:-----|:----|:-----------------------------|
| 0x0000 | (reserved)                     | N/A  | N/A  | N/A | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)      | 32   | 65   | 65  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)      | 48   | 97   | 97  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)      | 66   | 133  | 133 | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(Curve25519, HKDF-SHA256) | 32   | 32   | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(Curve448, HKDF-SHA512)   | 64   | 56   | 56  | {{?RFC7748}}, {{?RFC5869}}   |

### Marshal

For the NIST curves P-256, P-384 and P-521, the Marshal function of the
DH scheme produces the normal (non-compressed) representation of the
public key, according to {{SECG}}.

For the CFRG curves Curve25519 and Curve448, the Marshal function is
the identity function, since these curves already use fixed-length
byte strings for public keys.

### Validation of Inputs and Outputs

The following public keys are subject to validation if the curve
requires public key validation: the sender MUST validate the recipient's
public key `pkR`; the recipient MUST validate the ephemeral public key
`pkE`; in authenticated modes, the recipient MUST validate the sender's
static public key `pkS`.

For the NIST curves P-256, P-384 and P-521, senders and recipients
MUST perform full public-key validation on all public key inputs as
defined in {{keyagreement}}, which includes validating that a public
key is on the curve and part of the correct prime-order subgroup.
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
skR: 6bff5350645e59b1e770c8bb6f096dfa32285b2afebe46a0aad1aa5449b0fd07
skE: 950678c2be0e89a18336f691ab0500f916f539833348d733fb72285736dc57c4
pkR: 795339fc7ee4b5a7a8201333e4d3ec3e86fa47191418c22c385a2f78278d4f58
pkE: 3cbeea9a9201f8c73f8c42034479bc89238f40ae0141be2d71f027f4e728322b
enc: 3cbeea9a9201f8c73f8c42034479bc89238f40ae0141be2d71f027f4e728322b
zz: 10a0aa288ab7c79b301425524218b1b94ce402fdf7d2eddb0b7f3237adca041a
context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 89d98af366ff762958540e5f95bec339a0648ab998eb5478cf926c89df6d09c8
key: 040fe7da99ec895161393f2d73a94a7f
nonce: ac5579092b9f595a8ea0767b
exporterSecret:
878af0fa9d224285b4f235edeace7c5106afe3b70faa4d4bc9404ffd4d9ccef7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ac5579092b9f595a8ea0767b
ciphertext: 2bce2729aed1b2f6f78ef6efbf7e12278621c133a832954b1143d4b8142b
799239c24320be5a5496f8e0d2a341

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ac5579092b9f595a8ea0767a
ciphertext: 9acf2ad1060968afd1f2a78e6049052cda17ba2a9eca814fee44f022af29
9405af9c693a4f61e5b8ecf17adcd3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ac5579092b9f595a8ea07679
ciphertext: 19f3834823709aab655f68dc73e7434115f2a8c894337c7e6950609a7da5
8fedebe647975e8364c071f117b94b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ac5579092b9f595a8ea0767f
ciphertext: ec77c477aa6f7f1f274a32691af4dd89d85cd32731ee2c45ae42443e8cbe
447d6bf263107ebda6ecbf02ca4982

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: ca4f3cc7729370ba06000e22f960960b6fd95825a7089f8628e828040394b0d7
skE: 83c190cf68783aca23b11a05d5f5ba7304ea1663216e482fcea0cf0005a12768
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 62108b950534e73ad43bb6bc81c64c97cb07b0776c5e74a3582d46b9998cad42
pkE: 34b00ac4fdf44eedf049e5fc65eda29ba56e30cdb23f2a178cb31d0ff73a8203
enc: 34b00ac4fdf44eedf049e5fc65eda29ba56e30cdb23f2a178cb31d0ff73a8203
zz: 244c5ca7f3b31c790fd47a82dc7a997296d8dc620f02638c9f71a94db6e0acce
context: 00200001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 1b23d3c95a7ed347a48811f68ec222c06335df744443cda7ddf25dd2b9196942
key: 9482272e93fb020d5c67643913ed7623
nonce: 3536a91d9305541641c60445
exporterSecret:
86f9c2b2eefc2d27cb99b7884aeab917c4485f4a412f08f6c34dd698f7731d95
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3536a91d9305541641c60445
ciphertext: c29e41c6ab8f0eedff578325d8bfeeac30dadd3d4866778a50ce498b9db9
c6681d823f3106a8b82fc6593d9ea6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3536a91d9305541641c60444
ciphertext: ff9fa276e33791f49d7d69ce0a28738e42978dfb21f883fa5c9eba8d1882
b39964b452a36451d5e34648f433fb

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3536a91d9305541641c60447
ciphertext: 826eeaded14e593a010d1490981ac866d8e6a77fc84162ae32e828415cd2
3f39907ea40af0da8ee39fd69dfce5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3536a91d9305541641c60441
ciphertext: 6cfb05b250606088f89d9d3e567381348e5c3d4827c5a069e21c421e1bc8
398d08d5a9e057a028faa0b9aa3653

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: ce87b607782699cdebe49fa92a8839bc2cfbac2e8e4c37eb4ddadbff65b6bb4b
skS: 26f791ecdc89046c165218ae2be4ee92dc99493d4ecf8b09ef77a5008a2bcbf6
skE: c066a550223d20c92b5fde4d3bf4d452f44465db5e9ab52d4285c5fd61151655
pkR: 40f4ade76c041fd0077c3032ee8a15bef69ca593520858a761b1c2e88a8cbb08
pkS: 246f8b91ce7626393b50d1e740120babe0edee5d586ac56d2c45c0e191af3d07
pkE: 61011b5623cfc1a0be7d37a30708160fd231d9a345a0eb9873e9a5eece6bc702
enc: 61011b5623cfc1a0be7d37a30708160fd231d9a345a0eb9873e9a5eece6bc702
zz: b149bfe000403c6e8b4d27ec89d9b9f029ef401d5a5a7ca2e3f6c71f168dff33
context: 002000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: c36983e394e0eb39db323977d74699994b54f6de0d8d73e91475f8759459356d
key: 9bdf788ee1ff142f5ea59cb3da4df6b6
nonce: 834ab9df5a5578ba55a6e1f4
exporterSecret:
01709c5c584e8fbe022567d5f3003c095d3609cf7eebc32e641e73aa5a2cea29
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 834ab9df5a5578ba55a6e1f4
ciphertext: eb92566d739db3dc598b6518592a9c316c751bf70a93976b5474aaadfb5b
f3f1ee679325b778139e6ad7cb0a2f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 834ab9df5a5578ba55a6e1f5
ciphertext: b75d451142060e5405ec12e7a1920742177919ff994431543a7e51f5294b
5accc27ca0ac6551d57f16852fae0a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 834ab9df5a5578ba55a6e1f6
ciphertext: 44a0aaa234460047155e36f8857d40c818301c335509db1191ec64ea5208
aab527dd4204aa760501bbeb610b8b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 834ab9df5a5578ba55a6e1f0
ciphertext: 6a7b3ef1fb6184feb9bb049a60c98732e5a9b45fad505565d413a2c7e434
a88f2d9661f0f556fde9fcbee77fab

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 4b06c9b1621ed6deb74c142704100aedaf8256f56badc29f7b38bd05a1216bd1
skS: a11a9f0d43c646193e0719a967456e234b400c89d46283b5b5bd9d69d29a040d
skE: 88b66e17be56a26ef74bb11898606e4667f4545bf20a87bf46fc6d847b2caffa
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 8b7267d17bdabe270cfa3b32e1c50209a25df2a2af2c33aa209e94b361e93b7e
pkS: 0bb325a96c93ecf9273966a0e463a879a426fc6638196c585318433155958358
pkE: f08cb1ba1e3bdabc8c3cd1b3fb428399b362cf97075ede573caceef4dc12ec38
enc: f08cb1ba1e3bdabc8c3cd1b3fb428399b362cf97075ede573caceef4dc12ec38
zz: 696687480dccede0db16b187d1e52e2f6b9fbc18143488b9194b9eef99889bec
context: 00200001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 9b329dcf139b6b6c36c5225f367e347535a9425141cd7ebb4b9cb3d9920dab0d
key: e2de4e4bcc72692afe46c1b2e3c00fcf
nonce: 351d63cbdb0c0de3a1d76739
exporterSecret:
e6ae6998a9ff7f52fade7a0628fc68b0fec3979c04e27ac1b90fe44fffc80ca4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 351d63cbdb0c0de3a1d76739
ciphertext: 9425af7b9fd85c3d8d515123b2ed7941977090f2cabfd56a280d9a000aac
0e229128b2e382861765baae8d9100

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 351d63cbdb0c0de3a1d76738
ciphertext: c640e4fe32554d5af59d275c79d868456526467bbc4ad7ec5e0fa47cf025
6bab6d545c19debda8c138151dccc7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 351d63cbdb0c0de3a1d7673b
ciphertext: 47a477a7c1e24d0544e333533b13874ce3233b12881471ff04428da86dbe
3a273b5b8a5be1a40e4b302c7e452d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 351d63cbdb0c0de3a1d7673d
ciphertext: 6da969ddc3f5ad61e64cc719119a233c88cbf8f5895cd3a958462d12fb0a
83d676810b20d7398c8435c684dce7

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2f41ea103ed6e1755eab637299fd8e029c88a1c65651e0c46e1f0bba3c0ded61
skE: 207f762cab80cf022d00430a8f3cd7b51e9c568f704c50958c8bac5c76db3704
pkR: d245c899f96f1a6020abc575815a38154904be5c2f9b63d40a29aad29d5c4c63
pkE: 20a07a0dbe480b6c85c089ef107d597bc2e62f4d11200b36990ed94659408d6e
enc: 20a07a0dbe480b6c85c089ef107d597bc2e62f4d11200b36990ed94659408d6e
zz: 4687e3f5b6c49509e69d999867437cf3cf70f14725654d150976919f228e0115
context: 002000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: d706592a6d32ee2fc71f5d038bd48da3bbf9f65b15fe1624391143324e1138c0
key: 1ae5da29180eca56728431a1847571969903fa258e07b8c653d4a81a87335384
nonce: 0d76ed58debd727bf5bdee79
exporterSecret:
07754d31345bd9bad22bcb42e451401949e90d5ffbbed7e937ac26eed91e8a03
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 0d76ed58debd727bf5bdee79
ciphertext: 0e176ed49d87d28d65215a0cc047aeb778cdbf75fc7a80efa713100ef8cf
a350a436770a47c9334d0293f316d6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 0d76ed58debd727bf5bdee78
ciphertext: 44e56b634f5a5682c4889f0ccc135480adc8d7d0a92af9292779c57bb71c
288156e295ff8f298e0163e03a5367

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 0d76ed58debd727bf5bdee7b
ciphertext: 6b40be04332ef503da4f88ae1b38c6c275f07ba0255fd25a0b3d196e3915
235af5ab3258a2e1706c59827faccf

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 0d76ed58debd727bf5bdee7d
ciphertext: b14b1aff534ef08d85c9ea3ec30cb0bebe365bee3b66e61873af47bd7efe
8183b261fe1f378c2ac5dcffee47b7

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: cb645587480f06fb0ed030310e15a05d30c6b956bab1db89aae5568c13d26539
skE: 1ef96fefdb33405ceefadfa935fec0554f660a8b2ad7c6c77d6e2defce6707f3
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 95c4eda867719e56547ce6f8d7137923361360833b7f512ed9970a239f602536
pkE: 3f85fb361c154548dd1e302a03862dc84cf4d64866f0d6d204cf9187768d362e
enc: 3f85fb361c154548dd1e302a03862dc84cf4d64866f0d6d204cf9187768d362e
zz: 0cd021515da1dbaac825f1b868572680060814e23c4788157004761f08c20627
context: 00200001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 791b9e95957b44c2b453af9b75f19600e2da68359c44f1da2020af8c8020d65f
key: af70eae47785a564657f59f416717517c4f54fbdb02f1992a1ae0855d9651a00
nonce: d66a729ba2fedfb962a39fcc
exporterSecret:
65492d92e23f5af34623eb5d8ccc01bd8870d80ef57d0f5c02802d703ade3f9e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d66a729ba2fedfb962a39fcc
ciphertext: c3c03dd23782667d2ad61f5c0f98e5cdd894d9e045c9a8c364423e6e168f
9a837f84674de4ddcce401cbac01fb

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d66a729ba2fedfb962a39fcd
ciphertext: 747f4ad80247650395cd60bd01514f8cc4d4fcda32fd4e900232a1e95d76
92024698c0a7c727d371a5e6860a51

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d66a729ba2fedfb962a39fce
ciphertext: de19720abf6eea308f33e3ee008be4291328ca34f77434520b6b9ac708e1
710dd2c02594d0d13a9fb5846a1027

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d66a729ba2fedfb962a39fc8
ciphertext: 8f12eec7a8044ab89eb08ce95f47feabfed53b5c77b6d194c564580de31f
28066bce47a93da20595ad16110f4b

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: ed5ccc5bcc10479d853f7086e999ccb749994e34ca38dc912e80f83f8317f3eb
skS: c19fa03a5be446c58ddb5e61ac2f0de36ed8b256e96901cc7fbf2fa8fd12adbc
skE: 88900cf29c68a780a32d0e06370161d5e9008fe87fab6010bf36a4b2e1144420
pkR: 937f227b89a2af02eee2b20be33a26628839408bebcdc98d167d52b19ebd4b60
pkS: c34493274f47e45c6990c8ed243f9e97c163517d8e1e794686a6d4c65f342278
pkE: 2030974e85cdb830bd858e074292b2c26fddde3a1e59f98d5a72336b7006b370
enc: 2030974e85cdb830bd858e074292b2c26fddde3a1e59f98d5a72336b7006b370
zz: a1a438840c29793d607e57e20258f4d8de9dc73fd41c74bf6066f6a29aadf468
context: 002000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: c22e664ace27c51555c671b2ea5e01ff4718abd255153d90a0c7bbead1c89819
key: 339f1afcce7151df64a1ad81f9d440c19c1b6094ee70bbe1aa07cdaba4dff52e
nonce: 99bc47b9ff64fe5d7cb6626c
exporterSecret:
f279eda225a2fc0f0d5c6fd05e0944d3c6a46efa19fdefe58cafda9cbf409eb0
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 99bc47b9ff64fe5d7cb6626c
ciphertext: 1a64fa9db7227efa5e5da7ac636fb4012930bb560c2ac0dcc0ce5669b408
e1cae2747e28ffff118dee3e5b70b7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 99bc47b9ff64fe5d7cb6626d
ciphertext: 9fa37d4c3c9284a2ab6484d20d2cb12d81c652068601d9f3290136570f05
52eb371f61e10a1b83248058aee650

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 99bc47b9ff64fe5d7cb6626e
ciphertext: dbf4bc756ea6b99b1fe40e62710b63c55b558cff69479650eebf55be0515
a1a5ba2059191f07a033a178bea213

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 99bc47b9ff64fe5d7cb66268
ciphertext: e06fc71aab662c70f01b6f2edacb02e998f08b7cb817d451d6999d41fe8d
151b74ea69fc16fa250c6fc1582937

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 20995409cdd5f74c1d297615e3425b50ee3d2d3aa00185fa170070f5a1ac3565
skS: ad18bf5963db237e9854655fd471725140b954b47a1aa3c4daae46319a20a6d9
skE: 09e426e93d17784e8bc1c33d49b5455ddb64ce2a01fe57c96e7c1a29326d6be1
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 4b571141922ddbcc31ab12bf085a38273f88a629d37c74214f20b54c983b7135
pkS: dab3a9e523d1901fff4185ea1b7709c7f11b5d8402bf78d5e8c0bf624d11ac39
pkE: 73501e3c78366cc099a16d70bddb0a56de6b09e31c381e4e55f2dfb7d199c845
enc: 73501e3c78366cc099a16d70bddb0a56de6b09e31c381e4e55f2dfb7d199c845
zz: 7199bfbdcba083a33834efd66089d92df9ecff7c97939c27fe7c2c37118695a4
context: 00200001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: eb73646100ea14bd7ec372bd85a3335bbe48e8ac5a11b625f5e9e094f17b1eb4
key: 6420d13c7bc411aec12508c727030e118f8dcea52ff43611dc485082a3be3c8c
nonce: 3af643f2d0d6932ea161f542
exporterSecret:
75db2227c6d49bf98b9d281f815fd857d73b40a05a8434dec319432a2c7be567
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3af643f2d0d6932ea161f542
ciphertext: 3a3790634473cda58b6d9f910246f9a966cc69fdd7893ccaa27413cb08b2
2bb9c1c74397faeed3af873c231a3b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3af643f2d0d6932ea161f543
ciphertext: dc2d921ae925c2640fff932f40d214aae5e6783586a5d8e1833ed06bca81
afe73df5f44a5ced9f78b1d93dcd1e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3af643f2d0d6932ea161f540
ciphertext: 9448c28004f34963c0dee034ffbed9c262f97632204a0d02d109a0304f4c
127cfd370f2da501a40655f5d78d7b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3af643f2d0d6932ea161f546
ciphertext: 587eb68c51a73361832644b925574b724e600dc1c06278a302c9d6300e9d
0f09d0effba14883eae9f2e5b8f851

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: d06a6b68638b4411f60a0012a5d402b43ce5f486d4b4f73025aa6648e913dcc8
skE: ceb7b7afca75448a93c5d314b972e462005d44c01cde19d2fcc3828090ab29f8
pkR: 04dd7f873c1406373b0f7dddda8ae4bedfdf61aaa24c4461e99d01d7680c4d0ccf2
220e856f1d1c35ec4ee70f473b388e583bae27466884db31b354d60c6b8af25
pkE: 046ca106cbde787b348898e710d52e210605dd793cf82806650828854db6dfd2dd3
747a329a73672ae7f2a31787595eee28fb7a3bf44127b2207cc8b4986f560b7
enc: 046ca106cbde787b348898e710d52e210605dd793cf82806650828854db6dfd2dd3
747a329a73672ae7f2a31787595eee28fb7a3bf44127b2207cc8b4986f560b7
zz: 14e484f43ab7c236e350e0bedf5cbcbd2cf316828ae912416d8782c0b50a78b1
context: 001000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: fd24088bfb1a3af118b1b33a9fb3a4b493fda5a18686b6f79d181071cf44ddfc
key: e37b7bc05ba363b1883fd4823541f2d0
nonce: 59964db2f0aad1bae9986882
exporterSecret:
98edf3daecdaba549e015a141918bf21670a4a958f4e98af4cf09ffd7aad3bd6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 59964db2f0aad1bae9986882
ciphertext: 917719bbb23d239e39335e0bfc9480274bbfcb4bf384cc42a4b80c48d640
520437edfbf79ae3e8f09c1e568338

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 59964db2f0aad1bae9986883
ciphertext: ce29a7d5bb3a983280bfa755ec554588d4b4e1e036f1527e4a471f0cbb80
c4164ffc52bf881137431e730c36c4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 59964db2f0aad1bae9986880
ciphertext: fc2353acda8196e35d719cf2fc72607637f4695068d1f5fff11b8a305a2a
8123a32b4a4545ccd46ca70a084a0b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 59964db2f0aad1bae9986886
ciphertext: 0847051a7c69bf4f2efda796c53b5f72929eb3e2714fd9ef03b391824dbf
b83a50b4d89696233b543bf6965e72

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3e388352fcb3fcc81e53daa18f12cf0f8217e68e5ca1c07e126f63b0b8d8e121
skE: 96b8f2f473162a9132d37caa467ec6cdfa6ff240a334acdd2312438405d73a3a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04db6e26bfac931d98f78b3ae40dbfc9056942a477f795de26c93f6930e7e12a6af
0e07b9d9f27b001a1158b5681d41cda5e433bf43ec7955191d5a5c5860d7181
pkE: 04b21d027100cbd27356df80f9a0d5131cfce9f00b8761bf668adc0d4ad3e94e13d
887ec449ab865d41be2975a1bcd534af9e40d426afc71e3b613cb75bde9b912
enc: 04b21d027100cbd27356df80f9a0d5131cfce9f00b8761bf668adc0d4ad3e94e13d
887ec449ab865d41be2975a1bcd534af9e40d426afc71e3b613cb75bde9b912
zz: b4caeddb027e99c17e2c3346bd3740aa194ff80956ab752392ef7d4adfc7a2af
context: 00100001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: d3990d854ca301921cbfe2643cb93d2d20106c1adb9fa3b3a7fde7e6791970a5
key: a4756747feae0b7549e2d1cc9ddad33b
nonce: 88f67f96afb61e97708db372
exporterSecret:
e4d28c2d1aba2d1adc046cf3cb067ac9bdcfb4914dacf8d3d93fc9db3a74c127
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 88f67f96afb61e97708db372
ciphertext: 75118fab61a09c347949e2511c384b28abcd7f43b214e904da110e73f331
4d58cf033b2da3d4eebc22a25f3d73

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 88f67f96afb61e97708db373
ciphertext: 09d888341cf9e94770a4cb7853a99d172f7209d1da62c163b6b0817ff650
7195d3d628835e9c92ef8711a7846c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 88f67f96afb61e97708db370
ciphertext: 2b5101fc6f6658fc641683dd29f6551dd6337b616eedc8f2276d79ec4b29
b33176467cea8a09adfb3a11761fcd

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 88f67f96afb61e97708db376
ciphertext: a1de897e9793cd7ebe043e47243daaedb86dcd4ae92e5b69fc44864894e2
9bc17656847d20d1bfd1be3ad0f62a

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 45e98b84f4da1c2759945c228568b2fdaec3d971efd8254be686673a7274f441
skS: dc179156553920631ccdb130d812eddd10a1bffdde050859f955eeaa0c605958
skE: 87835e5a8aa57f49c4b92118e7d583e99d7e9ee6dfc1e3922a895ae9371396da
pkR: 047957bb57f2d1c89964a22250f12481346d3e0f2f0ecaf695264bc036f4146f31a
5202cc5c28ef6907b28b7783a8e4527b31306d997a124f28cbd4a73da308975
pkS: 04c8756e1dad51ec2ac847898f2ae84f09a695d6b88fd4a20b419fdf0d7f306abb5
5c21d4f0d286ac4e81ff9e5d04a5c7951f920ab61264269fbc9855889315610
pkE: 040ceb2a86ca0264ac80f751819d0a8e5e4085792aba3ac3a6d328e330d5999955c
acfbe23fa9acfa0dfc12c36618e913715f3c712127cb45258607878ea390824
enc: 040ceb2a86ca0264ac80f751819d0a8e5e4085792aba3ac3a6d328e330d5999955c
acfbe23fa9acfa0dfc12c36618e913715f3c712127cb45258607878ea390824
zz: db3f18d05fd65ec427d0421cd6cf42ef2d2f3d226837b7c8a7f23bcce44d380a
context: 001000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 5304eb5dd73d7532872a5a7bb46fab619469074608c9aced5baa4f55d67c8368
key: 9acef96ee37017cd008c1afe91dc687d
nonce: edb44d631ab5b98fbbb5ef43
exporterSecret:
75d4e5cf1dbe661b52e434bc9ef0460f01bb8805c8e003ec435d6e46040165fd
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: edb44d631ab5b98fbbb5ef43
ciphertext: d7ad6b6a2eb2dd6c4e2962da72483cbc8640c8ef694695f8e572a409ff5e
a59763b4c6abedf6b1952b360a11b9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: edb44d631ab5b98fbbb5ef42
ciphertext: ea507addb6e793f95ed5baee02c12f69c21dc450fdaecbe984b11baffbaa
6f7ed53dc968176273f80107dbf758

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: edb44d631ab5b98fbbb5ef41
ciphertext: 18b8dbb4401cc8e4cdfda0110885b944c99d2cc2d4c3ffd1364477bf216b
8a888aed79bdc24de733941fb8cd68

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: edb44d631ab5b98fbbb5ef47
ciphertext: cd3c3fdb1ba62f31b6bd421e288a583205bc1fb1f2bdf93699103cb856e1
0fc37c7e6b3f108d466cf8b0c7d39b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: c57ea45a0145d6542648b5ff63b840d24317d19686735ed76bf1cad830a01d99
skS: d484564e7214c27f5b1cba3fa52dae87105f0b94f17017e9b382deb44712c630
skE: b85fa3ef64cb0bc87cdbb7ff61d80508287ec2c7c71ef8224d1f573ee7802394
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 049f5d94ce657b219d909ad9bb48c2f18ba5d43b94006c87d1138b321b5bbb8fe9e
b3fee8619a45ef88d05d61a6ab85556f0c9615ddefe0b4e299a8a0f36a988eb
pkS: 04d6471d66fd83ff0bf9fd8d66aa325d85be94608f423bc4b63fd5fe51969d583c4
ae80155f6d45d9e1c31394a713bd53f59dfc27a6e1506e3f02fba77272de9ce
pkE: 04bb17408008d56469cabc2c06f58fa69013a188e7d43369f5af88a12b040e88384
41177833fab3131432ff6cdbeaf9287e36feaf3c6ce6734762ff7b4d905403c
enc: 04bb17408008d56469cabc2c06f58fa69013a188e7d43369f5af88a12b040e88384
41177833fab3131432ff6cdbeaf9287e36feaf3c6ce6734762ff7b4d905403c
zz: 39de797194df77c03a203b5d9c89f6772e3c852a8b6274d7650a43d35f2ea53e
context: 00100001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 887f14601cac865c008850a00d2bf21fa806384a8f3f283ca02b06c3949d2527
key: d8842be620c772bfafad295937aa0fa7
nonce: a899810323c1f9d75618d1b2
exporterSecret:
26910db7dca813db7ea202f28c53e78387c2998cc62aca75418ee143585e865b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a899810323c1f9d75618d1b2
ciphertext: 936de41d0f310329e236d2b8398e52ef028169613c68b4a4a2b18dd96d1b
22f649bb5d0b0296306fdba6c717e8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a899810323c1f9d75618d1b3
ciphertext: d5bcb47d0c31ebaa7395797fed5b3de000cd614b5779abe6c16026b6d9c4
9ae6563b74f6a8244bd2462c6ab9bc

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a899810323c1f9d75618d1b0
ciphertext: 5f61744d9c2939db2486f7d05f991c3f4724da7113ee48fe06d5a12a74c3
13124e41b6dc6fa7b623102277eed8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a899810323c1f9d75618d1b6
ciphertext: 6d737a8168a9aacaeaacb6022fce86051913963b7d7e96c2a2b76ad5bd23
0e8b85d5b8abb4a5be98db3b079ed7

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 1f903ecbb7a035780a11b8379076dd94c17caa4425111d729e0a5cc6a83ee18e
skE: 2dc2a51fd0075a5453ff2c71796b2871214308a8c1cfaf8b1970aa91e04568d4
pkR: 049574d6bd16a7596984781202fa898da9562d8e3bf565682f56f9454a3000affe8
eed29cd057d57e3ba87158856c8e2a53f7b5c80e6b67eebb01cabec1194625d
pkE: 04a6f2a7c859594b986bed92d05009315c0d7e5536e70214998c3b62137525951c6
4ee39fe65d097ea83be0c88756e7a9648d38bc353fb229637347654f34443bc
enc: 04a6f2a7c859594b986bed92d05009315c0d7e5536e70214998c3b62137525951c6
4ee39fe65d097ea83be0c88756e7a9648d38bc353fb229637347654f34443bc
zz: 5bfc502071b0d20252ff05ab5b4f2d5ee88ed12d6b8a4809e7467e150e8483ee
context: 001000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 09b0bb3a4cd50e1c46d69a1105c4b1e1768476b0437509ed62b7cd510ce4be8d
key: cbbe2a5919cfdc0f15eab0feac5f37878bc4ac6fd11b4b9092b0a081bfbd6e98
nonce: c2f370dfd7eebb3e9da176c0
exporterSecret:
f60a8c4eea3c47b031dd45d12b27c250d108feca7d89f6d66143bec65ad9c421
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c2f370dfd7eebb3e9da176c0
ciphertext: 74a686e25716be339692168dfb0f6638d34bb4ac364494d87601b21b7aaf
e9fdc1c788ca1c4a72ebcb2c42ab96

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c2f370dfd7eebb3e9da176c1
ciphertext: 2a5c2e24fee60a4a5c808ddb5d1e06d1f065b5d18c5a4abedbb40b0b73c6
9fe4b5df259098710bfeae1e228ab2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c2f370dfd7eebb3e9da176c2
ciphertext: cb7074f78e351e5d548abbd32df558f36d95a118c2718aeb37dab5e4db0b
929f9d3635f600ef601b58a7a98e59

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c2f370dfd7eebb3e9da176c4
ciphertext: 37026ef6ab825921664021d4c64049dabb0fa83cfd68e701ddb118d2c968
8aab726a79c1cab6f76953d60d5cd3

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2e1b6f5cf5ecd5b6a7982a1db600b30ac31a9967fa270a01e85dc38ab2ecc5d1
skE: 8e7b7ed4b96e77a4e20f3cf5e7ec2fb764ff1a87bf3b6043aedf2c11885a5a6d
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04c48eb2197766155047573d745e76743f18e6c3fb3e36fbe0c464019ef9f1671a3
1b45a461f9af74af9b8519f3341a822051b15e9512a8ac585ece985a6d9320a
pkE: 044238787ee4ef36241f087165c1ca8289efbb3335f79cfa6699a822a4d14f9b47e
9a1ab6c48a1035a1f2cf0ac36611e2653fe755cad57187fd6466b845ebc8302
enc: 044238787ee4ef36241f087165c1ca8289efbb3335f79cfa6699a822a4d14f9b47e
9a1ab6c48a1035a1f2cf0ac36611e2653fe755cad57187fd6466b845ebc8302
zz: 6f932cf45ccea32c16549a0a7e220b42362b4d2539e4d44855a0a265a4a76a00
context: 00100001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 4e62678a3af4dede1df38acd9621ce12e29b673c6e05044a62b9791479f1be17
key: b85dafd2b4e199929e9f45f1912e8f19e7500486001bc01e237d84269cb71644
nonce: c415bd6a0b406fbd20e955fb
exporterSecret:
ca5abae72b2807432715b482b8792f2ccc7ef5fb424df8dd07b7a3c956b77839
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c415bd6a0b406fbd20e955fb
ciphertext: 6d5b51cb42a730cd26eab15333c9f9aaecc457be4b60f18340d126e2a717
a6818b7eadb48eee2d919957c4cfd8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c415bd6a0b406fbd20e955fa
ciphertext: 6c811fd24dbf97b5d4e6e49da0d2df06610cf8834a5dc2fc39f5fe43ae38
569fab0311f1117ff7437aeac982b5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c415bd6a0b406fbd20e955f9
ciphertext: 3b5ad0d155ea9f958fc3cd3b6a5d1f5217bcd426bd7e406ebeceedff1db2
2b0cf67942bf4a52476d1cdccb734e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c415bd6a0b406fbd20e955ff
ciphertext: a0fb330a9e8d325fa26106dbc29759ce65713dc1c9644a9cc2e6f1513257
320becbf95a615863d541a9bd579ea

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 7c37ae67b79fcfa8d900bc372d1848026144f861ae06fc122f43fba6db90a477
skS: 388075725c8eb2f0abf3eb852f5c74a7ff51eaf86ec4b48001b470beb03210eb
skE: 2d2793e8d79a34775a5a448acdd91152209c6a6a8c6b77a5d0a52566d1432157
pkR: 046d99c26223a9db26f079c920c812938f10c8f88dc6eac04b2af21f235f4ab5e47
43d8808f983324b7763878f3ad24cbed5b1c0d2ff8935a5266dcfe8c3067ff9
pkS: 04a0680626cf3f83cedbe991f9319839ba47a6497169f45099e2d610cc8c7bb57db
1bb770dd43dc554d393f1150efce13e2d0da5f462cfc938cc84d5f354ed7260
pkE: 0469dc34ce088f75d98ca42c18d9e9ea2ba27ce05985664c041a8888bd9cd0a2e9c
4b59e4cb62f674ebf11388918acefb4b8776de13dbe386d7e1ece75ac002c42
enc: 0469dc34ce088f75d98ca42c18d9e9ea2ba27ce05985664c041a8888bd9cd0a2e9c
4b59e4cb62f674ebf11388918acefb4b8776de13dbe386d7e1ece75ac002c42
zz: 9e42fe6f26a97503f14d05462f288c6ba545574e1b7679040ab33d32d6672899
context: 001000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b24564499e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: adcda89b31a09601893c56f795a1b4438fa0446ae7ef2557c4389c0fb26e015c
key: ba768593cf999b3b0fefa88feb4f7d3d50426c089b3d04c698c23d1a5e89be39
nonce: 178edba4157cfbfa1f31282c
exporterSecret:
0075bcc52d0c71b6e42db3501c6b30c4b6864825f338ffd93806cd00c2ca0dda
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 178edba4157cfbfa1f31282c
ciphertext: cee59fa254436fa8bc443590a13c9c134c063fa573bd0f537f60260cbe65
858aeaadc281c8e40b2fa44b9a5b5e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 178edba4157cfbfa1f31282d
ciphertext: ce30bc62a155e7824a997e3a7e3e0c6b678876cfd847a518c0ff5bc6cb41
214262c19aa8b31903093d9aef87c5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 178edba4157cfbfa1f31282e
ciphertext: 1f8655a51be08a77e0beef70884bec753a8242910b85e768e2a9ba5215d9
895c9c507d1561e097cdc00d705c88

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 178edba4157cfbfa1f312828
ciphertext: 9bb9b4324ff581f71caba82d512ac12565b3a15f6df82c6db40a458c3599
654e3e2e7a2acd92df6a46f68f0bab

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 423e17d294b048c7c6637b7cb1f5c671589addd47c54c77bea4f20f6191c331e
skS: 4a7efec9179fa630745ce274ddb857eb089a82c2d26c138f59c66772de2d2e66
skE: 735ae0cd85690677cbd16d600d59375a51a6a3e90b1aaf123115ed0a3b8633f6
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04e705cb866ff3843a1fb4fca508438c42727a135f23e5c7227d61e9193826fbc62
0bfe351b663bbf8628e146e17a80ffbd801425c5c11d490c4d58bc7cb642cde
pkS: 04a06f9678c48a931b9851562b523895e944068c97e49e7061f9246c6f5fa4ccc78
4bce6f5b56e6b14c3403155138d47b831a16c6f9ea59b70c6f87044c9002ef1
pkE: 04986fefc865cd3f85df5053f781ecc2ffa88dab66aee5842f4180ea1d2ec52aec6
2aacea03b8e309d0a1ca18948282ab583133244cc074cdb119436a81314e892
enc: 04986fefc865cd3f85df5053f781ecc2ffa88dab66aee5842f4180ea1d2ec52aec6
2aacea03b8e309d0a1ca18948282ab583133244cc074cdb119436a81314e892
zz: 5118e65414059c89dffa20be7a1f2524dbeae9ff57e62155e938960193f7a9c8
context: 00100001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804be9e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: cccd751608af435c01fd5799ceb9080351630d730e637f32e0f58fae66ae0cf7
key: 07936e3fa00900ebd7afcb7a4594ebf91b0a73063909012e42cc90405239a5f0
nonce: 5bc6a7561e7f7d113b5eac65
exporterSecret:
57111f36ba886ae419f878d848372be0e2218797f3392a93bac941268a29a822
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5bc6a7561e7f7d113b5eac65
ciphertext: f346e80e5bded66c75a773c8cde836788f4f02ea0ab4ead39afd2ff1714b
357c38661895093b3c30e9b7a5d081

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5bc6a7561e7f7d113b5eac64
ciphertext: b239deedfdbda79cd41744c313a83b85ce31aa459db726ea857bab3d5855
0359f36090e5b77580627cd2e4f3bc

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5bc6a7561e7f7d113b5eac67
ciphertext: 8d1b55e981235aa5a3a1fd895b96c6dcab66ab9c03a8e84d36a6af42b0f5
d14bec477550ac144eaa3b61f8653e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5bc6a7561e7f7d113b5eac61
ciphertext: 8961c20bc955549cc90bee0aa4ae3337c75e986f045fd3e4aee2551e4b46
c9ab721ba11f036b8b902f8926f4a2

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 002aa2e30064cab7fdc507bde244dab87c9e57818bccd2cc939f3e93baf7d33a2fc
c79a4620adee21a9a8e167292759eaf46a6f9fae6a6395072ff4f0192533f6c15
skE: 006e68a2ac8ada049b4a3d60e6d4fb507da2da03b8fa8f8130ffe2caf4c4b1f5a58
24289de0ea93ba54ef9aa1459a58cd2c719e914e418e4186faf7437d713ac9290
pkR: 04009977c24bdbd144f85b279cea6b86a7d0e76e2052f3996f0cf4d5997e65521ee
9064273eb5bbe32929560ce712a64a8f5bdc67c354637e4986eb1fb48879190328b00144
ffb90fdea33cccb0d7b178ffefdbf04f2f444cf44dab0fe09000c4303faee69aad035042
1e117c47ce4e0d60d28db754ac05845278ee583afe930011a441b97
pkE: 04006c9a8726913695a00d2317c2f7bb41676d9e8cd617a4055be3879860655d0b8
9d19f3a5d95049ef6b1e16374a25ab052bc4904de7f60c54b041c4ffaaa04b374a901c8a
123f4cbd87aa033dfac33aaf470a9f67fad41e92a3b38a809d880ced47d6d691061e1f1c
55396cf7e7c2b94fe22d3b647a3882f0908672d643fd3c2ff44d050
enc: 04006c9a8726913695a00d2317c2f7bb41676d9e8cd617a4055be3879860655d0b8
9d19f3a5d95049ef6b1e16374a25ab052bc4904de7f60c54b041c4ffaaa04b374a901c8a
123f4cbd87aa033dfac33aaf470a9f67fad41e92a3b38a809d880ced47d6d691061e1f1c
55396cf7e7c2b94fe22d3b647a3882f0908672d643fd3c2ff44d050
zz: 5709f885d3ba51afbba0f95c53a15c166121eb9f5455936216d5b9e6389b89da26cc
09bbf59663ffbcd2afc4e5352efa1693231db22f2b875bdc1fafba990b8c8dc0
context: 001200030002008ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: af63b8ebadc920f64ef72139d75062ddb4a3936090dcf5575b45e9ba142a920f
c69198e8c572fb6bf0ac52fbe73ceacf0847cdc37661c54aaed2b40db184410e
key: 4c9ab5412ff38f921091a961270f36e94c19e715131c0c1983fe093b240332cd
nonce: 95499504fac597b5fb22f63e
exporterSecret: d13afebac0dc026b78be391ae84bd2365dff2716908a96c3eca7becf
c76a04b540a6d96d73f5de28630f5f218f1393427b980b6d1247871c3cd20e11c730a9df
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 95499504fac597b5fb22f63e
ciphertext: 84b5e258ba90b1d28f4a1541a920d4a43045e23edfe05afc1bf73a942365
dfad9931ec5dee8a018df5724b0302

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 95499504fac597b5fb22f63f
ciphertext: 1c7c397f84eb489ea5ee309c7ccd2e19631fe3863a9476b9e1fdba74663d
eb521f0e2af4e9e989071635a66aa3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 95499504fac597b5fb22f63c
ciphertext: 8fa0a1dbabf8c7a694bb5e34cfb19987b5b4a68b781949d6b7e89eaad544
62aaf9d483b7a06a14cc7ef35cef95

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 95499504fac597b5fb22f63a
ciphertext: 4ecf89759af0d7d985df303d3d3b7db79b939ce17d0c037c4ad954de2450
1e0928969a64456011a364afb524a1

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00e4c551d9bdeafaf85103bb54334b608499517ffb872603e2499c00df3d8edf443
a27b586e39070aadad484bc11de35edc15314950c07c2438ba70b3d2d03ce3b08
skE: 0180f17f80dc924d5a927a0e6515b492f91e252c8eba2045cc857efd774e63178ce
6c05b4941c5c3224a5bdbf8a4fb17755d0774cc0199ccc41b11a1e375fd78e1c4
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0401716219bb41f76dc0279dc4fb8023f233bb33c121f6467dc80a47bb45fb7ed34
12848d48bb0f90fd13ccc03f81bb06cc5f6156075e5fc13b4bca48df8bffb1aeed30101d
dd922f42488677f5ed4cf76744786e14d2438558923ea13e622bef74a8739cbb3e23c769
8cc5f3c44796022d557eb8bac4b5a10e823af456578e3d3dab2e2aa
pkE: 0400d6c2d02c182eb2de4b3e54c36d4458348f1c2c0925a122c2c5780317587da00
8802a09b6d43c63864866b7eb38d171c8232fd511952e698b6c0bf62c2618b75efa01412
60e6ec259693fdcc6edab6371ae651a2f6403e58d625d419152f9814ac116ce6191f84f2
6a8da15146fdced1fffbb7665a927fb617bacae8d467a61eb26a810
enc: 0400d6c2d02c182eb2de4b3e54c36d4458348f1c2c0925a122c2c5780317587da00
8802a09b6d43c63864866b7eb38d171c8232fd511952e698b6c0bf62c2618b75efa01412
60e6ec259693fdcc6edab6371ae651a2f6403e58d625d419152f9814ac116ce6191f84f2
6a8da15146fdced1fffbb7665a927fb617bacae8d467a61eb26a810
zz: 6309f2f23d1e41ba6947dd19afcb1a0a926c8263fe4cedc13bf513059286057df75f
653309a695ade41f625b2f2d7955db501081443edeaa22aa530287c63a99b943
context: 0012000300020119d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 6eca436fb8e26a25558f0c1dbe0d7a69669df3c8c1193ab83db7cb4d6c5c2c92
4a411793904d86c11da5ebee351eaf69d42ffb1c67cdc80c65499363479d57f7
key: 572e1d5753beb33facbd11fcce5e204b38032265aa5fe3fe7efd5222a834b8e1
nonce: 208a5332f18fcb491dfd03d2
exporterSecret: 228a0c910adc9a174835387b0e0e322502a7525a9d67903298fc3e2b
f523479cdbef32e3b9e2117c70fb805523088718ae440492823dd86a5cd86e296c1dda72
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 208a5332f18fcb491dfd03d2
ciphertext: 11dcaa11f54a9df5f6377a2c2207627cc70cbf2de02c5a0c5cafa10e8211
5bc442a53d4ea0fb0e0786d959941c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 208a5332f18fcb491dfd03d3
ciphertext: b3fc25828a3a0413c2979f1b89453f41acc00e99ddbb8f886d9422a03ebe
69119ef5df41065780bd6332046b27

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 208a5332f18fcb491dfd03d0
ciphertext: 4dc881b71a8eb00344a0e38ebcb72205d085a689eb70c8b68e1421ae67f0
d8a2ace64e0c186032ebb841e60a71

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 208a5332f18fcb491dfd03d6
ciphertext: 65f6ad1965eff37d60a541902dabe961db438521d6f652bcf52ccce3dc51
935ac59ebf2121d3ef99377ec2be1b

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0023fd6cb8049a59471d1f9b9e70fa6ad7559c31eb713035a391c9bd6a897b88c4d
702198409aa991b27cd5ef20189fffa9e8f1749aa3ed838403a9121550cfcd12f
skS: 011ae823a23c7158c26484f4cd920fa420334d5cd5464bcc47836c6f95065c219a0
2862a65e77e88e83f579911a19a5d7d793e966afee13745d7eaf25f1cd0b06166
skE: 01ec65484bd0b7fab4ace7cd95974a20938e6a8fba8249fe157001e1890093982de
26f168843960136db4839ee13fe7b44b70ee9cf1cbc19250023be7bc6501c6711
pkR: 0400c40b76c02904403bf7c4fde5ade2734e15af5374cc78787abd54ebbcb99f70a
813c858867dc473424dc331ba551a71671712dcfb34f950aee0c94d0e4f31f0b9ba01da3
141cb8a8c2d59baa4422d656921bededc7ac25ca2065f5a5c25cf64c419cad69dda065fc
373c9dedadf20cf0f1afa12c0cd454d195f1019783e50b30cf10ec3
pkS: 040120dfb33f4bbe15bc9fb6ecd32a5626e1296ebd29ef8efe063be4cf0a00c1da1
d08314f2ded8798395c8a5c56b23ab3a17e6f51cb8faa2b4a30b0ee50f7b7d5112100eca
43fb54bdda2a53c8e24a00172f8d97e94b53320a7d8deab0b932caac01707dc581951e2e
58f6f4a0409f900329802a8bb34d7760fde704f69591fb647b6a14f
pkE: 0400879234353d51b1ec396f3aa91dcdf6196f4e7b0c783299bee301ab731145a20
df2aedd7b55db9cfc4bd4384d6e6f8246f262a2ed8418cbd78b7fd523ef90fe29ad00cd8
d1d880062bc0c0227c17cf830e7ce34b5c3a02c70301f34a8efece3adc5915efafb63e4c
71e3159d2213d7cfd3eee7b3e3bdb9e1a099431b93c292443a8ef41
enc: 0400879234353d51b1ec396f3aa91dcdf6196f4e7b0c783299bee301ab731145a20
df2aedd7b55db9cfc4bd4384d6e6f8246f262a2ed8418cbd78b7fd523ef90fe29ad00cd8
d1d880062bc0c0227c17cf830e7ce34b5c3a02c70301f34a8efece3adc5915efafb63e4c
71e3159d2213d7cfd3eee7b3e3bdb9e1a099431b93c292443a8ef41
zz: 7c1e54dd3d564cab17188b328c6ce7838f19208f52edbbb7ade811dea6889372a064
697336f6becc10743a6118e7c8a9d1ad29a4d25fb9a40eb6e7cbfb370e606336
context: 001200030002028ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 53c0b9395423217b09c2e6e6873320d50c3704986f9422c9077ae99c33ccc682
a98fcd95480d1ed8b4b040f9e365581fde1b7dd0b82479c99730b12845216708
key: bde98a767875bc3519b83d21e9449816640c6fbf043f3ebc937419399abce741
nonce: 6202d27e24032212e44e4b4a
exporterSecret: eca31a5df0d2503c289ef336b3f4ae714569269bf5bce2660a6ddb7e
0d4668e2a881d9a48daed9f2a2a9e9af120f30655f4dc2c4ee70a8736e201ce12f2fb4da
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6202d27e24032212e44e4b4a
ciphertext: 7b8c7289e1d62a1534fd8807381c55775932b7cc854039500647aacf88bf
c2f960a4d9311c89ed66984a3390b6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6202d27e24032212e44e4b4b
ciphertext: 333b45e7093823eb574fbe090731d2732e2217bdb2f30f1fd02a9db3db61
d5682134dc5b5ee7fe301d672f190e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6202d27e24032212e44e4b48
ciphertext: d4396243f0480833a496ffb06310111537ad98bbdd3be20f8b96a7fec8eb
9e364b1012c9e861d233134e2bb916

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6202d27e24032212e44e4b4e
ciphertext: 49676c6ff735aff38c257e18ffb7435dc3a2715f41eaa8825e255f4c110a
1fa50049612c443d9ba9987f9438f6

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01be5770a1be893310dad0e627f6874d761c5ded462b41078b8dd704063d37d20cc
b1b7c8ad84f2d80a43a544f59a5e632764afcaad60e4cbcec4a09dfe09f6922e5
skS: 00a95ad16f9e36dcb505ad666a20e608012ea24945ebb87e7cd9c02cffd5b2937c1
55b36df2ce0d75f8120f0d9b431485f849a1426c273db8939b4bf0f71b7fdae1d
skE: 00ffa065b28e5191a88034567ce55c28183124db5e74ad4912d17930f95590c2ba9
9a1a3c3df5819867c0ae3bfec9f5f24a8a2c9d048a68ce2dd2bd4ec89d92d9975
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040134ae6d3f26a2f78eb38a44fe3c8471f79fde7e9e10538b7adf79d53de4c206b
99b9635c3e5b6b1dd7d0e4afd10268a18730e8f806c1eb4df1fed46badc3d97a0840158f
e6cee255f1815d50b85b3e4458290a039e2c147cd49dfc962d849cea5d40c802f93b2cc7
9c6bd844bd1593e3b9009a11e0e23ec8c413d11a9071095f12dd0a6
pkS: 040026b3e99bba2db1293db8b84f9e5ab500859d007dd547cb821fbfa2284daa1c8
1eb39f7d621c049c62b0dc66701421cec8f4da62e9d5107b744a5f4e0529e32d7820113c
06d63571ed5115780e24123841d6c21074234bfe84d02f2dbe53db6d641eab311790b0a8
055bc2bc71acefb4ca090f56f0f40d7cd6f8c436ff586b856c05ba0
pkE: 04010f80ec27248d56c23baddc5672602293689600f3d94cacb5eb1eafe0e2ec3eb
7c1b1e4a973f189201ab812182e3b74d226e27d25728a9fa8c48375305b84c3c7c400730
9bc8c42eef8825fcc472d21f606e0376f53c3188934134414c7fdc3ab762d4c231e43fd0
4b45f4570155298640277b0cfdea411371139fe298de56a07ca25ea
enc: 04010f80ec27248d56c23baddc5672602293689600f3d94cacb5eb1eafe0e2ec3eb
7c1b1e4a973f189201ab812182e3b74d226e27d25728a9fa8c48375305b84c3c7c400730
9bc8c42eef8825fcc472d21f606e0376f53c3188934134414c7fdc3ab762d4c231e43fd0
4b45f4570155298640277b0cfdea411371139fe298de56a07ca25ea
zz: 368b8c7e72bd2c871ee3297d7df2a573619357eb898064e0eac8a91a9fae09300799
4ec965154581311f407d71edf7e0bb2fa91a0b1570eb55e3892433b54ab93012
context: 0012000300020319d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8da4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 69d271ad890568b29f709c381c46fde50b4163db1f1f4e9fc524153b972b1cc6
339432085b73f77d98a64ecf3ec9f14495c79d0745dbace11ef36dd847b78fe2
key: 97f5b03be33254b12330419924f6bf9774657feef890cd391d1a15c66f8e2b90
nonce: e509babc787af3cdf2c12771
exporterSecret: fe0b5d02344838aa3a5bc9aee0e4ad44569a7c43a244952b39156281
2b36c698ef4adaa8af638fcd28363c751ec5a6c7d638f043306b32ce497fb274eb6b00ae
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e509babc787af3cdf2c12771
ciphertext: 2d768be2dda9697a453d5e59385038597d39237bfd8a9a41260f06f85ed7
e4a4a327336b467237f60f70ea87d1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e509babc787af3cdf2c12770
ciphertext: a0ece6e26b8dfeaf053f8d8d909b7211fe34b583b46aac811fb8b772c500
ba77126535acfeca50aa2316d7fc3d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e509babc787af3cdf2c12773
ciphertext: 4049de25f5aef61399fadd090bc970af50c138028bebc4b01c16583d0f7b
a51d9496aedae83500971e1d0c555f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e509babc787af3cdf2c12775
ciphertext: 023b686d0c9c60b70f5d62613ee130a51056bbc338ed8fe80bb85616fb66
bf06822118e77c3b60b62e654ed874

~~~
