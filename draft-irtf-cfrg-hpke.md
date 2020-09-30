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
 -  ins: B. Lipp
    name: Benjamin Lipp
    org: Inria
    email: ietf@benjaminlipp.de
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

  IEEE1363:
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
        org: Inria Paris

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

  IMB: DOI.10.1007/BF00124891

  LGR20:
    title: "Partitioning Oracle Attacks"
    date: To appear in USENIX Security 2021
    author:
      -
        ins: J. Len
        name: Julia Len
        org: Cornell Tech
      -
        ins: P. Grubbs
        name: Paul Grubbs
        org: Cornell Tech
      -
        ins: T. Ristenpart
        name: Thomas Ristenpart
        org: Cornell Tech

  TestVectors:
    title: "HPKE Test Vectors"
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/47118132e6913848eb1b4121370b1795d867a7bf/test-vectors.json
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

  WireGuard:
    title: "WireGuard: Next Generation Kernel Network Tunnel"
    target: https://www.wireguard.com/papers/wireguard.pdf
    date: 2020
    author:
      -
        ins: J. A. Donenfeld
        name: Jason A. Donenfeld

  NaCl:
    title: "Public-key authenticated encryption: crypto_box"
    target: https://nacl.cr.yp.to/box.html
    date: 2019

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
* TLS Encrypted ClientHello {{?I-D.ietf-tls-esni}}
* Protection of 5G subscriber identities {{fiveG}}

Currently, there are numerous competing and non-interoperable standards and
variants for hybrid encryption, mostly based on ECIES, including ANSI X9.63
(ECIES) {{ANSI}}, IEEE 1363a {{IEEE1363}}, ISO/IEC 18033-2 {{ISO}}, and SECG SEC 1
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
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - `GenerateKeyPair()`: Randomized algorithm to generate a key pair `(skX, pkX)`
  - `DeriveKeyPair(ikm)`: Deterministic algorithm to derive a key pair
    `(skX, pkX)` from the byte string `ikm`, where `ikm` SHOULD have at
    least `Nsk` bytes of entropy (see {{derive-key-pair}} for discussion)
  - `Serialize(pk)`: Produce a byte string of length `Npk` encoding the
    public key `pk`
  - `Deserialize(enc)`: Parse the byte string `enc` of length `Npk` to recover a
    public key. This function can raise a `DeserializeError` upon
    deserialization failure.
  - `Encap(pk)`: Randomized algorithm to generate an ephemeral,
    fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to `pk`
  - `Decap(enc, sk)`: Deterministic algorithm using the private key `sk`
    to recover the ephemeral symmetric key (the KEM shared secret) from
    its encapsulated representation `enc`. This function can raise an
    `DecapError` on decapsulation failure.
  - `AuthEncap(pkR, skS)` (optional): Same as `Encap()`, and the outputs
    encode an assurance that the KEM shared secret key was generated by the
    holder of the private key `skS`
  - `AuthDecap(skR, pkS)` (optional): Same as `Decap()`, and the recipient
    is assured that the KEM shared secret was generated by the holder of
    the private key `skS`
  - `Nsecret`: The length in bytes of a KEM shared secret produced by this KEM
  - `Nenc`: The length in bytes of an encapsulated key produced by this KEM
  - `Npk`: The length in bytes of an encoded public key for this KEM
  - `Nsk`: The length in bytes of an encoded private key for this KEM

* A Key Derivation Function (KDF):
  - `Extract(salt, ikm)`: Extract a pseudorandom key of fixed length `Nh` bytes
    from input keying material `ikm` and an optional byte string
    `salt`
  - `Expand(prk, info, L)`: Expand a pseudorandom key `prk` using
    optional string `info` into `L` bytes of output keying material
  - `Nh`: The output size of the `Extract()` function in bytes

* An AEAD encryption algorithm {{!RFC5116}}:
  - `Seal(key, nonce, aad, pt)`: Encrypt and authenticate plaintext
    `pt` with associated data `aad` using symmetric key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`. This function
     can raise a `NonceOverflowError` upon failure.
  - `Open(key, nonce, aad, ct)`: Decrypt ciphertext and tag `ct` using
    associated data `aad` with symmetric key `key` and nonce `nonce`,
    returning plaintext message `pt`. This function can raise an
    `OpenError` or `NonceOverflowError` upon failure.
  - `Nk`: The length in bytes of a key for this algorithm
  - `Nn`: The length in bytes of a nonce for this algorithm

A _ciphersuite_ is a triple (KEM, KDF, AEAD) containing a choice of algorithm
for each primitive.

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in {{ciphersuites}}.  Algorithm identifier
values are two bytes long.

Note that `GenerateKeyPair` can be implemented as `DeriveKeyPair(random(Nsk))`.

The following two functions are defined to facilitate domain separation of
KDF calls as well as context binding:

~~~
def LabeledExtract(salt, label, ikm):
  labeled_ikm = concat("HPKE-05 ", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "HPKE-05 ", suite_id, label, info)
  return Expand(prk, labeled_info, L)
~~~

\[\[RFC editor: please change "HPKE-05" to "RFCXXXX", where XXXX is the final number, before publication.]]

The value of `suite_id` depends on where the KDF is used; it is assumed
implicit from the implementation and not passed as parameter. If used
inside a KEM algorithm, `suite_id` MUST start with "KEM" and identify
this KEM algorithm; if used in the remainder of HPKE, it MUST start with
"HPKE" and identify the entire ciphersuite in use. See sections {{dhkem}}
and {{encryption-context}} for details.

## DH-Based KEM {#dhkem}

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- `GenerateKeyPair()`: Generate an ephemeral key pair `(skX, pkX)`
  for the DH group in use
- `DH(skX, pkY)`: Perform a non-interactive DH exchange using the
  private key `skX` and public key `pkY` to produce a Diffie-Hellman
  shared secret of length `Ndh`. This function can raise a
  `ValidationError` as described in {{validation}}.
- `Serialize(pk)`: Produce a byte string of length `Npk`
  encoding the public key `pk`
- `Deserialize(enc)`: Parse a byte string of length `Npk` to recover a
  public key (note: this function can raise an error upon `enc` deserialization failure)
- `Ndh`: The length in bytes of a Diffie-Hellman shared secret produced
  by `DH()`
- `Nsk`: The length in bytes of a Diffie-Hellman private key

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF. The function parameters `pkR` and `pkS` are deserialized
public keys, and `enc` is a serialized public key.
{{derive-key-pair}} contains the `DeriveKeyPair` function specification
for DHKEMs defined in this document.

~~~
def ExtractAndExpand(dh, kem_context):
  eae_prk = LabeledExtract("", "eae_prk", dh)
  shared_secret = LabeledExpand(eae_prk, "shared_secret", kem_context, Nsecret)
  return shared_secret

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def Decap(enc, skR):
  pkE = Deserialize(enc)
  dh = DH(skR, pkE)

  pkRm = Serialize(pk(skR))
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  pkSm = Serialize(pk(skS))
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def AuthDecap(enc, skR, pkS):
  pkE = Deserialize(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Serialize(pk(skR))
  pkSm = Serialize(pkS)
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret
~~~

The implicit `suite_id` value used within `LabeledExtract` and
`LabeledExpand` is defined as follows, where `kem_id` is defined
in {{kem-ids}}:

~~~
suite_id = concat("KEM", I2OSP(kem_id, 2))
~~~

The KDF used in DHKEM can be equal to or different from the KDF used
in the remainder of HPKE, depending on the chosen variant.
Implementations MUST make sure to use the constants (`Nh`) and function
calls (`LabeledExtract`, `LabeledExpand`) of the appropriate KDF when
implementing DHKEM. See {{kdf-choice}} for a comment on the choice of
a KDF for the remainder of HPKE, and {{domain-separation}} for the
rationale of the labels.

For the variants of DHKEM defined in this document, the size `Nsecret` of the
KEM shared secret is equal to the output length of the hash function
underlying the KDF. For P-256, P-384 and P-521, the size `Ndh` of the
Diffie-Hellman shared secret is equal to 32, 48, and 66, respectively,
corresponding to the x-coordinate of the resulting elliptic curve point {{IEEE1363}}.
For X25519 and X448, the size `Ndh` of is equal to 32 and 56, respectively
(see {{?RFC7748}}, Section 5).

It is important to note that the `AuthEncap()` and `AuthDecap()` functions of the
DHKEM variants defined in this document are vulnerable to key-compromise
impersonation (KCI). This means the assurance that the KEM shared secret key
was generated by the holder of the private key `skS` does not hold if
the recipient private key `skR` is compromised. See {{sec-properties}}
for more details.

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
include three authenticated variants, one which authenticates
possession of a pre-shared key, one which authenticates
possession of a KEM private key, and one which authenticates possession of both
a pre-shared key and a KEM private key. All authenticated variants contribute
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

A _context_ encodes the AEAD algorithm and key in use, and manages
the nonces used so that the same nonce is not used with multiple
plaintexts. It also has an interface for exporting secret values,
as described in {{hpke-export}}. See {{hpke-dem}} for a description
of this structure and its interfaces. HPKE decryption fails when
the underlying AEAD decryption fails.

The constructions described here presume that the relevant non-private
parameters (`enc`, `psk_id`, etc.) are transported between the sender and the
recipient by some application making use of HPKE. Moreover, a recipient with more
than one public key needs some way of determining which of its public keys was
used for the encapsulation operation. As an example, applications may send this
information alongside a ciphertext from sender to receiver. Specification of
such a mechanism is left to the application. See {{message-encoding}} for more
details.

Note that some KEMs may not support `AuthEncap()` or `AuthDecap()`.
For such KEMs, only `mode_base` or `mode_psk` are supported. Future specifications
which define new KEMs MUST indicate whether or not these modes are supported.

The procedures described in this session are laid out in a
Python-like pseudocode. The algorithms in use are left implicit.

## Creating the Encryption Context {#encryption-context}

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context. The key schedule inputs are as follows:

* `mode` - A one-byte value indicating the HPKE mode, defined in {{hpke}}.
* `shared_secret` - A KEM shared secret generated for this transaction
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared key (PSK) held by both the sender
  and the recipient (optional; default value "")
* `psk_id` - An identifier for the PSK (optional; default value "")

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

The `psk` and `psk_id` fields MUST appear together or not at all.
That is, if a non-default value is provided for one of them, then
the other MUST be set to a non-default value. This requirement is
encoded in `VerifyPSKInputs()` below.

The `psk`, `psk_id`, and `info` fields have maximum lengths that depend
on the KDF itself, on the definition of `LabeledExtract()`, and on the
constant labels used together with them. See {{kdf-input-length}} for
precise limits on these lengths.

The `key`, `nonce`, and `exporter_secret` computed by the key schedule have the
property that they are only known to the holder of the recipient private
key, and the entity that used the KEM to generate `shared_secret` and `enc`.

In the Auth and AuthPSK modes, the recipient is assured that the sender
held the private key `skS`. This assurance is limited for the DHKEM
variants defined in this document because of key-compromise impersonation,
as described in {{dhkem}} and {{sec-properties}}. If in the PSK and
AuthPSK modes, the `psk` and `psk_id` arguments are provided as required,
then the recipient is assured that the sender held the corresponding
pre-shared key. See {{sec-properties}} for more details.

The HPKE algorithm identifiers, i.e., the KEM `kem_id`, KDF `kdf_id`, and
AEAD `aead_id` 2-byte code points as defined in {{ciphersuites}}, are
assumed implicit from the implementation and not passed as parameters.
The implicit `suite_id` value used within `LabeledExtract` and
`LabeledExpand` is defined based on them as follows:

~~~
suite_id = concat(
  "HPKE",
  I2OSP(kem_id, 2),
  I2OSP(kdf_id, 2),
  I2OSP(aead_id, 2)
)
~~~

~~~~~
default_psk = ""
default_psk_id = ""

def VerifyPSKInputs(mode, psk, psk_id):
  got_psk = (psk != default_psk)
  got_psk_id = (psk_id != default_psk_id)
  if got_psk != got_psk_id:
    raise Exception("Inconsistent PSK inputs")

  if got_psk and (mode in [mode_base, mode_auth]):
    raise Exception("PSK input provided when not needed")
  if (not got_psk) and (mode in [mode_psk, mode_auth_psk]):
    raise Exception("Missing required PSK input")

def KeySchedule(mode, shared_secret, info, psk, psk_id):
  VerifyPSKInputs(mode, psk, psk_id)

  psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  info_hash = LabeledExtract("", "info_hash", info)
  key_schedule_context = concat(mode, psk_id_hash, info_hash)

  psk_hash = LabeledExtract("", "psk_hash", psk)

  secret = LabeledExtract(psk_hash, "secret", shared_secret)

  key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  nonce = LabeledExpand(secret, "nonce", key_schedule_context, Nn)
  exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)

  return Context(key, nonce, 0, exporter_secret)
~~~~~

See {{hpke-dem}} for a description of the `Context()` output.

Note that the `key_schedule_context` construction in `KeySchedule()` is
equivalent to serializing a structure of the following form in the TLS presentation
syntax:

~~~~~
struct {
    uint8 mode;
    opaque psk_id_hash[Nh];
    opaque info_hash[Nh];
} KeyScheduleContext;
~~~~~

### Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
to the holder of a given KEM private key.  The `SetupBaseS()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The KEM shared secret is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

The parameter `pkR` is a public key, and `enc` is a
serialized public key.

~~~~~
def SetupBaseS(pkR, info):
  shared_secret, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, shared_secret, info, default_psk, default_psk_id)

def SetupBaseR(enc, skR, info):
  shared_secret = Decap(enc, skR)
  return KeySchedule(mode_base, shared_secret, info, default_psk, default_psk_id)
~~~~~

### Authentication using a Pre-Shared Key {#mode-psk}

This variant extends the base mechanism by allowing the recipient to
authenticate that the sender possessed a given PSK. The PSK also
improves confidentiality guarantees in certain adversary models, as
described in more detail in {{sec-properties}}. We assume that both
parties have been provisioned with both the PSK value `psk` and another
byte string `psk_id` that is used to identify which PSK should be used.

The primary difference from the base case is that the `psk` and `psk_id` values
are used as `ikm` inputs to the KDF (instead of using the empty string).

The PSK MUST have at least 32 bytes of entropy and SHOULD be of length `Nh`
bytes or longer. See {{security-psk}} for a more detailed discussion.

~~~~~
def SetupPSKS(pkR, info, psk, psk_id):
  shared_secret, enc = Encap(pkR)
  return enc, KeySchedule(mode_psk, shared_secret, info, psk, psk_id)

def SetupPSKR(enc, skR, info, psk, psk_id):
  shared_secret = Decap(enc, skR)
  return KeySchedule(mode_psk, shared_secret, info, psk, psk_id)
~~~~~

### Authentication using an Asymmetric Key {#mode-auth}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkS)` produces the correct KEM shared secret
only if the encapsulated value `enc` was produced by
`AuthEncap(pkR, skS)`, where `skS` is the private key corresponding
to `pkS`.  In other words, at most two entities (precisely two, in the case
of DHKEM) could have produced this secret, so if the recipient is at most one, then
the sender is the other with overwhelming probability.

The primary difference from the base case is that the calls to
`Encap()` and `Decap()` are replaced with calls to `AuthEncap()` and
`AuthDecap()`, which add the sender public key to their internal
context string. The function parameters `pkR` and `pkS` are
public keys, and `enc` is a serialized public key.

Obviously, this variant can only be used with a KEM that provides
`AuthEncap()` and `AuthDecap()` procedures.

This mechanism authenticates only the key pair of the sender, not
any other identifier.  If an application wishes to bind HPKE
ciphertexts or exported secrets to another identity for the sender
(e.g., an email address or domain name), then this identifier should be
included in the `info` parameter to avoid identity mis-binding issues {{IMB}}.

~~~~~
def SetupAuthS(pkR, info, skS):
  shared_secret, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth, shared_secret, info, default_psk, default_psk_id)

def SetupAuthR(enc, skR, info, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, shared_secret, info, default_psk, default_psk_id)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
  shared_secret, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, shared_secret, info, psk, psk_id)

def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, shared_secret, info, psk, psk_id)
~~~~~

The PSK MUST have at least 32 bytes of entropy and SHOULD be of length `Nh`
bytes or longer. See {{security-psk}} for a more detailed discussion.

## Encryption and Decryption {#hpke-dem}

HPKE allows multiple encryption operations to be done based on a
given setup transaction.  Since the public-key operations involved
in setup are typically more expensive than symmetric encryption or
decryption, this allows applications to amortize the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this encryption must be
stateful. Each of the setup procedures above produces a context object
that stores the AEAD and Secret Export parameters. The AEAD parameters
consist of:

* The AEAD algorithm in use
* The key to be used with the AEAD algorithm
* A base nonce value
* A sequence number (initially 0)

The Secret Export parameters consist of:

* The ciphersuite in use
* The exporter secret used for the Secret Export interface; see {{hpke-export}}

All of these parameters except the AEAD sequence number are constant.
The sequence number is used to provide nonce uniqueness: The nonce used
for each encryption or decryption operation is the result of XORing
the base nonce with the current sequence number, encoded as a
big-endian integer of the same length as the nonce.  Implementations
MAY use a sequence number that is shorter than the nonce (padding on
the left with zero), but MUST raise an error if the sequence number
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
and decryption nonces align. If `Context.Seal()` or `Context.Open()` would cause
the `seq` field to overflow, then the implementation MUST fail with an error.
(In the pseudocode below, `Context.IncrementSeq()` fails with an error when `seq` overflows,
which causes `Context.Seal()` and `Context.Open()` to fail accordingly.) Note that
the internal `Seal()` and `Open()` calls inside correspond to the context's AEAD
algorithm.

~~~~~
def Context.ComputeNonce(seq):
  seq_bytes = I2OSP(seq, Nn)
  return xor(self.nonce, seq_bytes)

def Context.IncrementSeq():
  if self.seq >= (1 << (8*Nn)) - 1:
    raise NonceOverflowError
  self.seq += 1

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
  if pt == OpenError:
    raise OpenError
  self.IncrementSeq()
  return pt
~~~~~

## Secret Export {#hpke-export}

HPKE provides an interface for exporting secrets from the encryption `Context`
using a variable-length PRF, similar to the TLS 1.3 exporter interface
(see {{?RFC8446}}, Section 7.5). This interface takes as input a context
string `exporter_context` and a desired length `L` in bytes, and produces
a secret derived from the internal exporter secret using the corresponding
KDF Expand function. For the KDFs defined in this specification, `L` has
a maximum value of `255*Nh`. Future specifications which define new KDFs
MUST specify a bound for `L`.

The `exporter_context` field has a maximum length that depends on the KDF
itself, on the definition of `LabeledExpand()`, and on the constant labels
used together with them. See {{kdf-input-length}} for precise limits on this length.

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
indicated by "..." depend on `MODE` and may be empty. `SetupBase()`, for example, has no
additional parameters. `SealAuthPSK()` and `OpenAuthPSK()` would be implemented as follows:

~~~
def SealAuthPSK(pkR, info, aad, pt, psk, psk_id, skS):
  enc, ctx = SetupAuthPSKS(pkR, info, psk, psk_id, skS)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def OpenAuthPSK(enc, skR, info, aad, ct, psk, psk_id, pkS):
  ctx = SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS)
  return ctx.Open(aad, ct)
~~~

# Algorithm Identifiers {#ciphersuites}

## Key Encapsulation Mechanisms (KEMs) {#kem-ids}

| Value  | KEM                        | Nsecret  | Nenc | Npk | Nsk | Reference                    |
|:-------|:---------------------------|:---------|:-----|:----|:----|:-----------------------------|
| 0x0000 | (reserved)                 | N/A      | N/A  | N/A | N/A | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)  | 32       | 65   | 65  | 32  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)  | 48       | 97   | 97  | 48  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)  | 64       | 133  | 133 | 66  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(X25519, HKDF-SHA256) | 32       | 32   | 32  | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64       | 56   | 56  | 56  | {{?RFC7748}}, {{?RFC5869}}   |

### Serialize/Deserialize

For P-256, P-384 and P-521, the `Serialize()` function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}. `Deserialize()` performs the
uncompressed Octet-String-to-Elliptic-Curve-Point conversion.

For X25519 and X448, the `Serialize()` and `Deserialize()` functions
are the identity function, since these curves already use fixed-length byte
strings for public keys.

Some deserialized public keys MUST be validated before they can be used. See
{{validation}} for specifics.

### DeriveKeyPair {#derive-key-pair}

The keys that `DeriveKeyPair()` produces have only as much entropy as the provided
input keying material. For a given KEM, the `ikm` parameter given to `DeriveKeyPair()` SHOULD
have length at least `Nsk`, and SHOULD have at least `Nsk` bytes of entropy.

All invocations of KDF functions (such as `LabeledExtract` or `Expand`) in any
DHKEM's `DeriveKeyPair()` function use the DHKEM's associated KDF (as opposed to
the ciphersuite's KDF).

For P-256, P-384 and P-521, the `DeriveKeyPair()` function of the KEM performs
rejection sampling over field elements:

~~~
def DeriveKeyPair(ikm):
  dkp_prk = LabeledExtract("", "dkp_prk", ikm)
  sk = 0
  counter = 0
  while sk == 0 or sk >= order:
    if counter > 255:
      raise DeriveKeyPairError
    bytes = LabeledExpand(dkp_prk, "candidate", I2OSP(counter, 1), Nsk)
    bytes[0] = bytes[0] & bitmask
    sk = OS2IP(bytes)
    counter = counter + 1
  return (sk, pk(sk))
~~~

where `order` is the order of the curve being used (this can be found in
section D.1.2 of {{NISTCurves}}), and `bitmask` is defined to be 0xFF for P-256
and P-384, and 0x01 for P-521. The precise likelihood of `DeriveKeyPair()`
failing with DeriveKeyPairError depends on the group being used, but it
is negligibly small in all cases.

For X25519 and X448, the `DeriveKeyPair()` function applies a KDF to the input:

~~~
def DeriveKeyPair(ikm):
  dkp_prk = LabeledExtract("", "dkp_prk", ikm)
  sk = LabeledExpand(dkp_prk, "sk", "", Nsk)
  return (sk, pk(sk))
~~~

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

For X25519 and X448, public keys and Diffie-Hellman outputs MUST be validated
as described in {{RFC7748}}. In particular, recipients MUST check whether
the Diffie-Hellman shared secret is the all-zero value and abort if so.

## Key Derivation Functions (KDFs) {#kdf-ids}

| Value  | KDF         | Nh  | Reference    |
|:-------|:------------|-----|:-------------|
| 0x0000 | (reserved)  | N/A | N/A          |
| 0x0001 | HKDF-SHA256 | 32  | {{?RFC5869}} |
| 0x0002 | HKDF-SHA384 | 48  | {{?RFC5869}} |
| 0x0003 | HKDF-SHA512 | 64  | {{?RFC5869}} |

### Input Length Restrictions {#kdf-input-length}

This document defines `LabeledExtract()` and `LabeledExpand()` based on the
KDFs listed above. These functions add prefixes to their respective
inputs `ikm` and `info` before calling the KDF's `Extract()` and `Expand()`
functions. This leads to a reduction of the maximum input length that
is available for the inputs `psk`, `psk_id`, `info`, `exporter_context`,
i.e., the variable-length parameters provided by HPKE applications.
The following table lists the maximum allowed lengths of these fields
for the KDFs defined in this document, as inclusive bounds in bytes:

| Input            | HKDF-SHA256  | HKDF-SHA384   | HKDF-SHA512   |
|:-----------------|:-------------|:--------------|:--------------|
| psk              | 2^{61} - 91  | 2^{125} - 155 | 2^{125} - 155 |
| psk_id           | 2^{61} - 93  | 2^{125} - 157 | 2^{125} - 157 |
| info             | 2^{61} - 92  | 2^{125} - 156 | 2^{125} - 156 |
| exporter_context | 2^{61} - 121 | 2^{125} - 201 | 2^{125} - 217 |

This shows that the limits are only marginally smaller than the maximum
input length of the underlying hash function; these limits are large and
unlikely to be reached in practical applications. Future specifications
which define new KDFs MUST specify bounds for these variable-length
parameters.

The values for `psk`, `psk_id`, and `info` which are inputs to
`LabeledExtract()` were computed with the following expression:

~~~
max_size_hash_input - Nb - size_label_rfcXXXX - size_suite_id - size_input_label
~~~

The value for `exporter_context` which is an input to `LabeledExpand()`
was computed with the following expression:

~~~
max_size_hash_input - Nb - Nh - size_label_rfcXXXX - size_suite_id - size_input_label - 2 - 1
~~~

In these equations, `max_size_hash_input` is the maximum input length
of the underlying hash function in bytes, `Nb` is the block size of the
underlying hash function in bytes, `size_label_rfcXXXX` is the size
of "HPKE-05 " in bytes and equals 8, `size_suite_id` is the size of the
`suite_id` and equals 9, and `size_input_label` is the size
of the label used as parameter to `LabeledExtract()` or `LabeledExpand()`.

\[\[RFC editor: please change "HPKE-05" to "RFCXXXX", where XXXX is the final number, before publication.]]

## Authenticated Encryption with Associated Data (AEAD) Functions {#aead-ids}

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-128-GCM      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-256-GCM      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |

# Security Considerations {#sec-considerations}

## Security Properties {#sec-properties}

HPKE has several security goals, depending on the mode of operation,
against active and adaptive attackers that can compromise partial
secrets of senders and recipients. The desired security goals are
detailed below:

* Message secrecy: Confidentiality of the sender's messages against
  chosen ciphertext attacks, i.e., IND-CCA2 security
* Export key secrecy: Indistinguishability of each export
  secret from a uniformly random bitstring of equal length, i.e.,
  `Context.Export` is a variable-length PRF
* Sender authentication: Proof of sender origin for PSK, Auth, and
  AuthPSK modes

These security goals are expected to hold for any honest sender and
honest recipient keys, as well as if the honest sender and honest
recipient keys are the same.

As noted in {{non-goals}}, HPKE does not provide forward secrecy.
In the Base mode, the secrecy properties are only expected to
hold if the recipient private key `skR` is not compromised at any point
in time. In the PSK and AuthPSK modes, the secrecy properties are
expected to hold if the recipient private key `skR` and the pre-shared key
are not both compromised at any point in time.

In the Auth mode, sender authentication is generally expected to hold if
the sender private key `skS` is not compromised at the time of message
reception. In the AuthPSK mode, sender authentication is generally
expected to hold if at the time of message reception, the sender private
key skS and the pre-shared key are not both compromised. However, it is
important to note that the DHKEM variants defined in this document are
vulnerable to key-compromise impersonation attacks {{?BJM97=DOI.10.1007/BFb0024447}},
which means that sender authentication cannot be expected to hold in the
Auth mode if the recipient private key `skR` is compromised, and in the
AuthPSK mode if the pre-shared key and the recipient private key `skR` are
both compromised. NaCl's `box` interface {{NaCl}} has the same issue. At
the same time, this enables repudiability.

Applications that require resistance against key-compromise impersonation
SHOULD take extra steps to prevent this attack. One possibility is to
produce a digital signature over the Auth and AuthPSK `enc` output using
a sender's private key, as a proof of possession.

Given these properties, pre-shared keys strengthen both the authentication and the
secrecy properties in certain adversary models. One particular example in which
this can be useful is a hybrid quantum setting: if a
non-quantum-resistant KEM used with HPKE is broken by a
quantum computer, the security properties are preserved through the use
of a pre-shared key. This assumes that the pre-shared key has not been
compromised, as described in {{WireGuard}}.

It is shown in {{CS01}} that a hybrid public-key encryption scheme of
essentially the same form as described here is IND-CCA2-secure as long as
the underlying KEM and AEAD schemes are IND-CCA2-secure. The main
difference between the scheme proposed there and the scheme in this
document (both named HPKE) is that we interpose some KDF calls between
the KEM and the AEAD. Analyzing the HPKE instantiation in this
document therefore required verifying that the additional KDF calls
do not cause the IND-CCA2 property to fail, as well as verifying the
two additional properties noted above (export key secrecy and
sender authentication).

This work has been done for the case where the KEM is DHKEM, the AEAD is
any IND-CCA2-secure scheme, and the DH group and KDF satisfy the
following conditions {{HPKEAnalysis}}:

- DH group: The gap Diffie-Hellman (GDH) problem is hard in the
  appropriate subgroup {{GAP}}.
- `Extract()` and `Expand()` (in DHKEM): `Extract()` can be modeled as
  a random oracle. `Expand()` can be modeled as a pseudorandom function,
  wherein the first argument is the key.
- `Extract()` and `Expand()` (elsewhere): `Extract()` can be modeled as
  a random oracle. `Expand()` can be modeled as a pseudorandom function,
  wherein the first argument is the key.

In particular, the KDFs and DH groups defined in this document (see
{{kdf-ids}} and {{kem-ids}}) satisfy these properties when used as
specified.

The analysis in {{HPKEAnalysis}} demonstrates that under these
constraints, HPKE continues to provide IND-CCA2 security, and provides
the additional properties noted above. Also, the analysis confirms the
expected properties hold under the different key compromise cases
mentioned above. The analysis considers a sender that sends one message
using the encryption context, and additionally exports two independent
secrets using the secret export interface.

The table below summarizes the main results from {{HPKEAnalysis}}. N/A
means that a property does not apply for the given mode, whereas `y` means
the given mode satisfies the property.

| Variant | Message Sec. | Export Sec. | Sender Auth. |
|:--------|:------------:|:-----------:|:------------:|
| Base    | y            | y           | N/A          |
| PSK     | y            | y           | y            |
| Auth    | y            | y           | y            |
| AuthPSK | y            | y           | y            |

If non-DH-based KEMs are to be used with HPKE, further analysis will be
necessary to prove their security. The results from {{CS01}} provide
some indication that any IND-CCA2-secure KEM will suffice here, but are
not conclusive given the differences in the schemes.

In addition, both {{CS01}} and {{HPKEAnalysis}} are premised on
classical security models and assumptions, and do not consider
adversaries capable of quantum computation. A full proof of post-quantum
security would need to take appropriate security models and assumptions
into account, in addition to simply using a post-quantum KEM. The hybrid
quantum-resistance property described above, which is achieved by using
the PSK or AuthPSK mode, is proven in {{HPKEAnalysis}}; in a quantum
setting, the remaining security level is smaller and defined by the
post-quantum security level of the AEAD scheme.

## Security Requirements on a KEM used within HPKE

A KEM used within HPKE MUST ensure the following to avoid identity
mis-binding issues: The KEM shared secret computed by `Encap()` and `Decap()` MUST
depend explicitly on the KEM public key `pkR` and the encapsulated key `enc`,
as observed in {{S01}}. The KEM shared secret returned by `AuthEncap()` and `AuthDecap()`
MUST explicitly depend on the KEM public keys `pkR` and `pkS` and the encapsulated
key `enc`. This is usually implemented by including these values explicitly into
the context of the key derivation function used to compute the KEM shared
secret. This is also how DHKEM meets the requirement.

## Security Requirements on a KDF {#kdf-choice}

The choice of the KDF for the remainder of HPKE SHOULD be made based on
the security level provided by the KEM and, if applicable, by the PSK.
The KDF SHOULD have at least have the security level of the KEM and
SHOULD at least have the security level provided by the PSK.

HPKE's `KeySchedule()` uses `LabeledExtract()` to convert an arbitrary-length
PSK into a fixed-length PSK. This is necessary because of the
restrictions on the key in HMAC's indifferentiability theorem {{HMAC}}.
A future instantiation of HPKE MAY omit this line and use the PSK
directly as salt for the computation of `secret`, if: `Extract()` is not
instantiated by `HKDF-Extract()` and there is an indifferentiability theorem
for `Extract()` without restriction on the key's length.

## Pre-Shared Key Recommendations {#security-psk}

In the PSK and AuthPSK modes, the PSK MUST have at least 32 bytes of
entropy and SHOULD be of length Nh bytes or longer. Using a PSK longer than
32 bytes but shorter than `Nh` bytes is permitted. A PSK that is longer than
`Nh` bytes or that has more than `Nh` bytes of entropy, respectively, does
not increase the security level of HPKE, because the extraction step involving
the PSK only outputs `Nh` bytes.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see {{?RFC5869}}. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret
`shared_secret` and has access to an oracle that allows to distinguish between
a good and a wrong PSK, it can perform PSK-recovering attacks. This oracle
can be the decryption operation on a captured HPKE ciphertext or any other
recipient behavior which is observably different when using a wrong PSK.
The adversary knows the KEM shared secret shared_secret if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

To recover a lower entropy PSK, an attacker in this scenario can trivially
perform a dictionary attack. Given a set `S` of possible PSK values, the
attacker generates an HPKE ciphertext using each value in `S`, and submits
the resulting ciphertexts to the oracle to learn which PSK is being used by
the receiver. Further, because HPKE uses AEAD schemes that are not key-committing,
an attacker can mount a partitioning oracle attack {{LGR20}} which can recover
the PSK from a set of `S` possible PSK values, with |S| = m\*k, in roughly
m + log k queries to the oracle using ciphertexts of length proportional to
k, the maximum message length in blocks. The PSK must therefore be chosen with
sufficient entropy so that m + log k is prohibitive for attackers (e.g., 2^128).

## Domain Separation {#domain-separation}

HPKE allows combining a DHKEM variant DHKEM(Group, KDF') and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to `Extract()` and `Expand()` inside DHKEM and the remainder of HPKE have
different prefix-free encodings for the second parameter. This is
achieved by the different prefix-free label parameters in the calls to
`LabeledExtract()` and `LabeledExpand()`. This serves to separate the input
domains of all `Extract()` and `Expand()` invocations. It also justifies modeling
them as independent functions even if instantiated by the same KDF.

Future KEM instantiations MUST ensure that all internal invocations of
`Extract()` and `Expand()` can be modeled as functions independent from the
invocations of `Extract()` and `Expand()` in the remainder of HPKE. One way to
ensure this is by using an equal or similar prefixing scheme with
an identifier different from "HPKE-05 ". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info`, `psk_id`, and `psk`.

The string literal "HPKE-05 " used in `LabeledExtract()` and `LabeledExpand()`
ensures that any secrets derived in HPKE are bound to the scheme's name,
even when possibly derived from the same Diffie-Hellman or KEM shared
secret as in another scheme.

## External Requirements / Non-Goals {#non-goals}

HPKE is designed to be a fairly low-level primitive, and thus does not provide
several features that a more high-level protocol might provide, for example:

* Downgrade prevention - HPKE assumes that the sender and recipient agree on
  what algorithms to use.  Depending on how these algorithms are negotiated, it
  may be possible for an intermediary to force the two parties to use
  suboptimal algorithms.

* Replay protection - The requirement that ciphertexts be presented to the
  `Context.Open()` function in the same order they were generated by `Context.Seal()`
  provides a degree of replay protection within a stream of ciphertexts
  resulting from a given `Context`.  HPKE provides no other replay protection.

* Forward secrecy - HPKE ciphertexts are not forward-secure. In the Base and
  Auth modes, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In the PSK and AuthPSK modes, a given
  ciphertext can be decrypted if the recipient's public encryption key and the
  PSK are compromised.

## Metadata Protection

The authenticated modes of HPKE (PSK, Auth, AuthPSK) require that the recipient
know what key material to use for the sender.  This can be signaled in
applications by sending the PSK ID (`psk_id` above) and/or the sender's public
key (`pkS`).  However, these values themselves might be considered sensitive,
since in a given application context, they might identify the sender.

An application that wishes to protect these metadata values without requiring
further provisioning of keys can use an additional instance of HPKE, using the
unauthenticated Base mode.  Where the application might have sent `(psk_id, pkS,
enc, ciphertext)` before, it would now send `(enc2, ciphertext2, enc, ciphertext)`,
where `(enc2, ciphertext2)` represent the encryption of the `psk_id` and `pkS`
values.

The cost of this approach is an additional KEM operation each for the sender and
the recipient.  A potential lower-cost approach (involving only symmetric
operations) would be available if the nonce-protection schemes in {{BNT19}}
could be extended to cover other metadata.  However, this construction would
require further analysis.

## Designated-Verifier Signature

The Auth and AuthPSK modes can be used to construct a lightweight
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
and calls `Open()` with the provided ciphertext.  If the AEAD authentication passes,
then the signature is valid.

This scheme reuses the authentication scheme underlying the AEAD algorithm in
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
* Nsecret: The length in bytes of a KEM shared secret produced by the algorithm
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

The authors would like to thank
David Benjamin,
Benjamin Beurdouche,
Frank Denis,
Kevin Jacobs,
Raphael Robert,
Michael Rosenberg,
Michael Scott,
Steven Valdez,
Riad Wahby,
and other contributors in the CFRG for helpful feedback that greatly improved this document.

--- back

# Test Vectors

These test vectors are also available in JSON format at {{TestVectors}}.
Note that the plaintext is the same for each test vector. Only the nonce
and AAD values differ. In these vectors, `GenerateKeyPair()` is implemented
as `DeriveKeyPair(random(Nsk))`.

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: f28b02a334b98190e210297dc55951a4ffa8f0ad88d8610ca59d3704b1870beb
seedR: 786b486b443b9b02b4ad58f40b2ff25849d90bfec2243e58633fb44a57b00ceb
enc: c8a9520417e8cb7aa606c36a5bef9f5d2db300b9ab9c908b4cb588f51418d351
shared_secret:
033ca57fd76a73143519a19cd609fd2a2cf92b3926c10932802cf892dff579ad
key_schedule_context: 000c085d4e6d2e6a568b5dcf334f7badd56222cd79f2ac98b6
f99059f311c3f16a44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 9079eed1a86fddafb4d54e3573290177e44c47ad794f57fac1ead0502a547185
key: f73c75623822357593eccf35565b07f4
nonce: 7530e5ad98ff49a760326cb9
exporter_secret:
84b158baff479e2a1e0392d62f6ebcd5ef5ce6002b7a06d1c91d62c9612761ba
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7530e5ad98ff49a760326cb9
ciphertext: ba37f063ff1588b5225183b560063fc7bbae3b1f68aa2d00a45c73785fde
279d73028bfcdf105ccc1e93ae2d31

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7530e5ad98ff49a760326cb8
ciphertext: 6d813dccd6dc596210df5b9039a327c9a5701e14713372462cbf217ae015
0f89a4da8ec0244e7982b8596d90da

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7530e5ad98ff49a760326cbb
ciphertext: e99a14841a146ee8a0a4af7d307e68eb4cd39825654581f5a51057d2a1ee
d00c1eefdbe380ab493fc05a3c7c2e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7530e5ad98ff49a760326cbd
ciphertext: a136531ddebd292e8d2e149637a54525bfe764a6d562da42bd3a9233f9f8
2ea54d5511773cf81621f16891d143

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9da790f0f5bd38cc45fe13a081ac2bacfd9aa1c4362c5d348b6e4e59b877af63
seedR: 32609274ec453b7f258339da213ff7c68eb977b9b547890fe539296af5984675
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 9b5e9865a1c24671d04b2c5aabb2602fff5f5d3e1f4555e277c915cd7bf72f6c
shared_secret:
39803a02e487ed0031a44e32992f871ae3468675aaeb6d8a388acb0cf25058d3
key_schedule_context: 01512564fc13bf3387a7d73eb72eb6b62766480582bfe146c4
e5afb8788652269644c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 87fcd9c63597e76d0bb679dca03319fedc7df78dc06576d80d1c123813bac5ff
key: f0529818bc7e87857fd38eeca1a47020
nonce: 4bbcb168c8486e04b9382642
exporter_secret:
4f6180a492f231ea225cc480330b83ce4adc2d772b14c71540ddb6a8e15ecbaf
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4bbcb168c8486e04b9382642
ciphertext: 9076d402a8bacf1721ce194185de331c014c55dd801ae92aa63017a1f0c0
dff615d4bcbc03d22f6d635e89b4c2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4bbcb168c8486e04b9382643
ciphertext: b967d791c8c76642412391f95f837901d5be59a920febe3926b95844d22b
39a021bf4163a4a01f3c9f9e54282c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4bbcb168c8486e04b9382640
ciphertext: 28517083266209c250650f31b3b5a190de8ee9ca4915539ea2e470cb6d55
d58144d065aba3a5f7e18e4298e2cf

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4bbcb168c8486e04b9382646
ciphertext: 399da0c52f7f782d4499b9d95bce10cfaeae2ab938258ad42960ac6b378f
fd01cd51cc5d3ef13573e16a8b9dcd

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 8cd54d6536fe84dbb73baa50e4133b2768dc37198b33119d519adfab1d29c81f
seedR: 514abde1fbf0cc1f7a3b7925e9adfefb47eb6c05d2d065f00ca8fef9c5e0ba8b
seedS: 83e9388d489c77541e029ed59b61849fcc6c3d294834f5e1c80f1ae7d47acdb4
enc: b180823d50c43db84181492af5e16683e47401fd6e17f93ca1975a30c8cfc942
shared_secret:
b14167da17b5ad1af8660ac9a74772abb7943256c20214709ed304a0a23fb49c
key_schedule_context: 020c085d4e6d2e6a568b5dcf334f7badd56222cd79f2ac98b6
f99059f311c3f16a44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 888adc8ff839abf725eae164e00e04ac13a6046fcfee7222269c3ff3cf594797
key: 69100ccf464b54fade60956ab2618038
nonce: 6e356f49030c57eff82b2426
exporter_secret:
b69d1ef605c37c8add2d0efbaee390a778ae4095d28d640cae76eb82d2370d7a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6e356f49030c57eff82b2426
ciphertext: 1b26bd977a3446d4e4220f505fd233512945f6474930a43d529a1c11fb05
4673cfe928e5183a426f324038a55d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6e356f49030c57eff82b2427
ciphertext: 13653c349b2ec7a4047df5016b7ca2d64ea193899cc3f8ef8024b177df91
b45d72ae7ba3bb75ef0300b9b54e30

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6e356f49030c57eff82b2424
ciphertext: ed28bf8fc6b7afc58b5976d38e0fcb271e0f73db12611f66b980531f172d
b149a5161f13ba069b5cbec1fcbb9d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6e356f49030c57eff82b2422
ciphertext: 5afef1bd8482b7a9e060c1a3efe161bce49b2a443209386d3605e219590a
7d40325f79c59b368b8264505f5315

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: b321172d30f49e8e619683eb7592860330ca15103f30c534f99454ab48d21414
seedR: cee74b37d0b8b201afee7292da24f25e736558f0c9220545a31bf42173087e23
seedS: 2f9d7dd9c59c0ba8841b5c6180860d495199ba5ab7253cb487614419f40ce912
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 31f6611448e60b4468a7ac9859f9353ad6be8344c9c397deaf4fb6f23e93a044
shared_secret:
65d158c887941bf849ef2bd899122dcced892110f76df6a42da7aac962e5f757
key_schedule_context: 03512564fc13bf3387a7d73eb72eb6b62766480582bfe146c4
e5afb8788652269644c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: da19ab925dc85b72639db04cf51de24cc59b3e1273dd25a691e1ba7b3c73052e
key: eb2883950fc52fde002cc9cd3d0f8f72
nonce: cd68a6b2a78419242f6424d3
exporter_secret:
7f852d021b288e074fd44ea858b6bff4cfe3dffa1598430d4eaa150426d58a94
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: cd68a6b2a78419242f6424d3
ciphertext: 2f3d607c4578812d702cec5d990d2a9ff406d6a25c8075d426d2f1c892bd
2bbdde497818c17d539a791c5c3db7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: cd68a6b2a78419242f6424d2
ciphertext: 06a68e123f5de46ea252a0bc918590c3471b6dd3d69de692f269b6c8551d
6927c4c208f863de9c7abab5150399

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: cd68a6b2a78419242f6424d1
ciphertext: 67eecc4ee6c0845e59fe8b95309b83df5371920bef770ca4db6228e86a55
ebc71dce846481a7e80a2329a76874

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: cd68a6b2a78419242f6424d7
ciphertext: ed6add176620ac83e1805d482af33c499871b22da625481c39f4cb74ac8b
bc0141e26960faac988608fc5465e2

~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9642242fc302242383e6ef8b85e78b4e56eaa5d24c1af83132967ea7b0a819e9
seedR: c48cc08d30f3bdb765838f2e2e77b606d172dab365ab593072bbe30919d3a82a
enc: 5bab0d0e25704bcb6f84e49fe903f58f8f2b08896b96a4e066f5160ce9262056
shared_secret:
48cdc94d425139ce11b744ba87c7e0b8e6d02deff0ee0ec0b2f70b45f667f336
key_schedule_context: 00cbe688614d6e54c26594f3c118e6cb1a01f6c6572a9112dc
2687bd3e8b1e6ba06da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: bb7c7017f42d1cd3189f5b027faf060e96c08ae74a667bcc5a6e2a629d86a496
key: 41b9ddb0860f38a6c53e16f07400d1abe84aef89d14138bdc90732d60d1364c9
nonce: b66635166986772f1a51765b
exporter_secret:
8859392535ad0f6e4b236d3eb906973095963835dc2f3d0a12be386dbc7f08ee
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b66635166986772f1a51765b
ciphertext: 3b68969454f0da698358337aabf28fe57992314080348f00aa805a109052
aac0f98049ccaf64c61cac4940d32a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b66635166986772f1a51765a
ciphertext: 80f2cb38776d101e962bfeafb7a68ba49977cd542d9c94bfa41aab3543d3
94a87d666a17705ab99388bab39423

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b66635166986772f1a517659
ciphertext: a6fe02bae1d5e181d511e3994b8adb083db3dd20f25ed57b3ee6fd1bf477
997754e1ddaedf0ec9084df7e94c11

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b66635166986772f1a51765f
ciphertext: 7e64397a366f3b53f4d06e0d6533c2b9732a9ae5c299c4b31293b90815d6
20d53d70d60735feba99cc3e9b15dd

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 7bd62eb7739d793c87e31d63b46a3cefadb414afbfe5ad39c087f6536c632ad4
seedR: 5cd8081031ae6263f172d92274623f07e61e1033fb38d713dcc73b32ecb4b554
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: c845bb1a71cddce15fb436b34650355f3e78c6467da14c5c142ba94174011237
shared_secret:
95555ae17aed6f91319452df79ac08a38af542664c9e65bfb1c61d55f55ea53d
key_schedule_context: 01f5f7e2ba59c3ff0cff51f71c4204fcfc76c95f778b37ccdc
6a83b3df36c33e7b6da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: c31d04a2398b3a7a4ef25c1f956c0f626e068a195b63969b5e022a4723974aa8
key: 09e3bb59594d59f6dccc64d7cdcfc659056e26d2b06f75d17466ce43677d0a0e
nonce: 7eff5cb474f3b746109e6ae8
exporter_secret:
60f5fe76e2699f98c19eab82fecf330b990ac32694a8e40e598e2326d0e29150
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7eff5cb474f3b746109e6ae8
ciphertext: 0fc1f8d64819f83662a87c90e9cc1dea46c47ceb93663898d199b0555c90
90bfa78373fb1c739bfe8aba262bdf

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7eff5cb474f3b746109e6ae9
ciphertext: f1676a5df76016c5bcf72da06b7674d4e3c8b8aab8f524bc16026730bb3b
66ffdc2f28291b1434720eab2c92c0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7eff5cb474f3b746109e6aea
ciphertext: e6fafbce944c89ae6cf9c3114680267226738e8cffd67b252712aaa449a3
1958596f2f5a39b93bb2d7d0c236e6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7eff5cb474f3b746109e6aec
ciphertext: 928481abd91f0c38310b3e314d167fa92d584b774745a1beee8ffdce21d2
4fb34bb57c066540a45ab77e6dd1d9

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: fc23903cf547715009c965553b51f3c1ccfeb722d48af56e6fe1d7c543a2ab24
seedR: 6deb991137e679fde5e23b47a879f33380f6daccc0f1014bf469275d3fd65cc9
seedS: a14eb8deb9caceda2b421745959bb43cfa91851c960e12764b6333d7a6ad37ba
enc: f8efb7024c7a6be9b4a82ec49ea333b975bc5f9581d97b0be8f4afbc70cefc62
shared_secret:
a49abf4b375f089c7ac1cacc59f61f57917cc23ac32724d4c974f0485026baef
key_schedule_context: 02cbe688614d6e54c26594f3c118e6cb1a01f6c6572a9112dc
2687bd3e8b1e6ba06da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: accc2495a55b033aaaf89d64e5e3f971e232deaf866cce209eebdaa8b3b53a01
key: 35954ba742888d312ad5c6c6f1f847a133070d6177dcadb6a35ea8a7169e80a3
nonce: 05e2b39adac37613ed2b3672
exporter_secret:
777796a7a2937fe3f2d1ccb4f5412adf8b8df2cbcf9ad392fdac8db3e8e171fc
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 05e2b39adac37613ed2b3672
ciphertext: 0a09241277af67c052da8153e9c60b5fa45728b6f01d3f63a77aaf0da847
ffa41b1b8b9306e8fd46582e859889

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 05e2b39adac37613ed2b3673
ciphertext: 9951bd579fe6abc58a5910304386cec633a65fffa45e2c437f7336427dbc
2760a152a14b0c7aec309396a68d59

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 05e2b39adac37613ed2b3670
ciphertext: 98d2774acad749e00c0cce42bf70a997fabffeb4675de69c5efd5a3b87ba
b270c9a6f0cfb178b4f5780f417613

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 05e2b39adac37613ed2b3676
ciphertext: 775e775f0e735d3ddc383c109a734c4d954ba72c8c5f843eef441dcad4da
22ec1fea9d4c4ae301451b0d127c09

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: ca878dbeb446cdcb0e855a953035197ae3114b4bad0548e108ced3371b3bb6c3
seedR: 5cffd4ae57207d974af52b9d3bd9e524d0165955f964e24ed916bbb4854f4e75
seedS: 58bbfd87b5c311193cac5ff53ef28ec564b238e2bcb989eecab340c8eb2c919a
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: b9d6fb3a46dde90bece75186f7a918a8255133b8ccbfddb1e01121f65b860e4b
shared_secret:
f8c061fd99bc869b4b438cc92b327d53f04401e9e3a79dbdda4adc7037c53cc6
key_schedule_context: 03f5f7e2ba59c3ff0cff51f71c4204fcfc76c95f778b37ccdc
6a83b3df36c33e7b6da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 65d47b38e52c1404c5508ef29639657e7179227eca8377cf2f6613541bc3a125
key: a3bb906b717001c3b1b5ab38dff0a94d089accecd1d6a2f778c8a4996efb81d5
nonce: ef2b3014ed64a35062937f37
exporter_secret:
5c00b2ee3ee9e7c6caaed82be22eeb07177a0f59177468d02c5a213f385dcec7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ef2b3014ed64a35062937f37
ciphertext: 711dc4f4e79469a5e113867a41ad638e5a01443ad26bb9404c1e9c9d0e14
275e3da89fa51ced93f408e44fd52c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ef2b3014ed64a35062937f36
ciphertext: 09d8240d0fd61a7c38d77924ec3b80e8c3ee2bf653c52ddc5d1a29f56afd
cdcb9b35b2f2a977728d7e9e9a4674

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ef2b3014ed64a35062937f35
ciphertext: f3d7ff285a4680c3969de85f80d27068310d9f52c0fde9a8ea89b8413fdd
2ce0f1b7eb1df46cc76d8c802e8ab5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ef2b3014ed64a35062937f33
ciphertext: 5b0906c8859028b21d063a7fdb2fbd97c2c28c47bf6211908a95c3d9fac6
319d9a49851725708bd461733543f2

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 751c47cc15a0824999cd6bc9f5ad03f131841c245cec89066a7612a0141a0f84
seedR: 896313940ea96eadddfacb7fdcb59831fd2420da1abfc11ad5721220f1a2bd61
enc: 04c3a974e42246acba5d65b7acde0d9718b2d9ee1738465be496b28203a35cc90a3
b2c2fd2d1015b3940e068402c3eb5d777e2d387338fddbf2935e5e58a1e5380
shared_secret:
9ef5d8cb9235818b356404d047db0b2b8fbebef433913e185949e9bb40d0189a
key_schedule_context: 00c14ae6a0da7c6764c62eba270ec0cc28b5b568b4849a9b59
425c08860800fad8a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 95ca08e6acc4da80bdfdd93a762c190db9f7b022d0ffd43f2e79316b87221588
key: 631c9f9f84621eb9396a554cfe12e0ce
nonce: e1bb091541dcd804c3010098
exporter_secret:
778d8d94ec910a4ec77b6a6ec4421660901f110134347efdb20ddebdabb9afb8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e1bb091541dcd804c3010098
ciphertext: 4084eebb5d8531469590284f46993b2714528b24726966378c9327bd2a62
d2fa4760ca4130f0458ab895b71dce

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e1bb091541dcd804c3010099
ciphertext: 78e2a27d72d0a16b3dd28fe7b92f1f9ce0c6b74d1e3e7186394f2db59030
1ce00e4d17b84bb0f4c537b0e85ae6

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e1bb091541dcd804c301009a
ciphertext: 7d5e549a6a6e407ae3fcad6e9ffd9bc36ec4f30eefc9e367f87f238bcc9e
3b012f271eb68e7161b46c9014aeeb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e1bb091541dcd804c301009c
ciphertext: 5a6bfc6bb63f24aa8d43e56c0918ff9092047029ceae6a4eab7c1c808b93
7ba3f5f040108fc8a7fa9079b5599b

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 256f6f6c1490fa26c6e96c722d67e700914ee1f65d47c4ee2f72208df563ca49
seedR: ff39ba7aae2a33034c4052a92f1bd9b1409c4494ce25972f6b7c4fee7bff8fd7
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 045031b6f6d7b90a3e145e800a0fb142c1880580ab81aff6e3f0fc40b920a0cdac7
d8f9c4ca5a3baaa346ac27a3d72d608b5c503595debbda3a176d34e19d56ca0
shared_secret:
dc9e87081e93d16db6bac8ca600863d5cd6a1a40a91da147c644bdb35f965856
key_schedule_context: 018c27d3410cb79f908302ae06a67ad4c6f971cc37f64c2380
7cb4de4adeaa7d76a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: a0b48511d76765ec0df8bbc9db9bfdd2927abd77ed4df1166116e3155684a8bb
key: 8d0dc124bbfe13e4ca468b13dcf4372f
nonce: 6da984dd38f0c4dcc2ea52c8
exporter_secret:
9aae234e8e43f4eba3b812f84f69b95c9c1959a27e57740e00dac8214513407b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6da984dd38f0c4dcc2ea52c8
ciphertext: d76acd309737e40a85f97e1c2e82cbc06ee3f4975d8ec6cc2dbaf8eb216b
76ce98d6a74ba79cfce0bbc2da48f9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6da984dd38f0c4dcc2ea52c9
ciphertext: a70acdb5b98f4419306f799c585f58276f3f3dc4354e31a192e1a39589e0
88d0db74154b71736e0b837eb19a8b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6da984dd38f0c4dcc2ea52ca
ciphertext: 479d409357a6314a0cf5d15e71b3326d6fd140719b2862ac0478a9a9b077
c4d32103672a6b2302d762a682a956

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6da984dd38f0c4dcc2ea52cc
ciphertext: b1f671032cc4c91fcc1c4f37243fc249f961f2c7365e90f559edacda386c
a45d7dadfdb56e82f998e39b240a31

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 74639e8833745bf63e419254073c2c673b48c556d7bc33203195911ecf3e2833
seedR: 5ad276d3d660b3a9e2709e090c1eb8130a4bd89d8bcbbd4cf27e8a391970bda8
seedS: 3a83c5ce06c273de116d327e59f6d3c4c6c84c89535514839794a0582e7088d0
enc: 0455897e8acebf6ea183bdf59b1fe3cbacbee01cfeca9d1aabafda749062b7c0cd9
9835183616aa6a3e39e447e33452b5ca20c623d88d67e9696d86a57dee18100
shared_secret:
8b3be45236e33c3a8c835770d470cd7c7feab715f0806b4e2e49decff52fb498
key_schedule_context: 02c14ae6a0da7c6764c62eba270ec0cc28b5b568b4849a9b59
425c08860800fad8a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: dc1ffd7926621e29e496b70fd1f40301b10d08c05ed7b2a9399e765c9747041b
key: 157a0d9d2e52cdb96a2d48a4987a16dc
nonce: ee345b28835fc9ccaed82e15
exporter_secret:
37af9e34a76af0cefea880748f17c94e8171c47c28bbcec7db7fe214ef92c6ae
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ee345b28835fc9ccaed82e15
ciphertext: 7ca04a80d131599b987a90161cb03d2bac29e8ba4199d3076fdeb13f26ca
8d0a832e924c820a72783f73caf439

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ee345b28835fc9ccaed82e14
ciphertext: 8edce20b5abd689d0a5d0fd9e0ad2d7714777bfbdfe0d1bdd6dc94c9b983
e337027783d9c7717d4409b1acd393

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ee345b28835fc9ccaed82e17
ciphertext: 5c416a61b947423f878c646dfdd381d643aa79e79fbd6bbc50d91d071cec
0f60e2ddf84b74c060fc56ccaa4335

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ee345b28835fc9ccaed82e11
ciphertext: dd2c50216ac74512a82a6879f353ee8f0110e41479a8d112a93edd632463
0404534d1b63bc68737f48bc3572ba

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9292bee07456cae31c04af06a7f5f755b0dadd3ced76a8531862fdb5f35b2ee3
seedR: 14568ba460f050b3336e179971cb82b6c4b3a364f60785ec7efd653d2e94caca
seedS: 1c0677fd043c02471df2d5b3e1e4a23c2861d42792a5a93938102d76cab59946
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0473c412f452b000d2ed3e5837d495713cfe412a6a992f1aaad260f4f78417963fd
09ba868058db51caa9cd2453a67dcff653b02793723e23df5ab2fb8826166db
shared_secret:
48bdade5406a5cd77dac590ae30200e0e78b6ea4fc46420d48d9ac1d56d4b430
key_schedule_context: 038c27d3410cb79f908302ae06a67ad4c6f971cc37f64c2380
7cb4de4adeaa7d76a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: e7ac260b5fcfe87022c0675fe07f95ecf4f733ab0fa11215d25f3a62d6358ed6
key: 526bc2fbb3f0462027f006936141f02e
nonce: 5e667af597332f2b5e918be6
exporter_secret:
3631f02c63988baa7f0c9041464f5e59305fad1e8c2696815f8d7d752209b893
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5e667af597332f2b5e918be6
ciphertext: 291993377f38a21b6cf51addf44576d28967ea4298a03d0e097eed1bcd9e
7dd23b7dfb1115c998a6fbc26b7c7a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5e667af597332f2b5e918be7
ciphertext: 23b91d0d70b5cf996370889e65557917e3115d3729f50e9d59d791dc9861
a934e920a6ef5512240039d84dc3af

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5e667af597332f2b5e918be4
ciphertext: 332d6daaa25f5b2a66177931a6a7c532a06a50aba2cef45f283f82ad5059
f14cfcf205ac28e46169b817179da6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5e667af597332f2b5e918be2
ciphertext: a3dfbe1584d52ca87bd20c90a9fc2c5cc4aabbf810d99b5bcf17861af23d
029fcb95a8c92b8c6f2d0ba20b8c62

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA512, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 6ce3c5c35742759a08bd6494466284a33885b4461ada948232e5c0cc519a1007
seedR: 978dd2906cc9ecf100f413f7489be444f4a1392cbad6ef16e348c48a3ae8e24e
enc: 04c6212e11a355a9d5944757b55f85af45e412b90e658b66bd8ce8eb5347464a92b
4de971fb75416f130f2812bbef0ee53615286d6b60f6121a7d1daff5b81c7dd
shared_secret:
9a8ed6c0ee76323f33739de22dedfff2ea54c17e6e617f17e58a0ef021147ce7
key_schedule_context: 0059a145bcce1c1c862714bcd04c342351f917429e57578e3a
2fa684c7ed0403ba264455f90835145bd18f39bfadab2d3808163e74fc91c733021e758f
5b70c2668c9942e377e9f72fa4152c161bfba6c407fe5ee3d6517b56634fdf07ade5b4fc
b1358e1f01175ac61ef5c191ba765599e625e92cd4623fea16bbe3a0ca2db1df
secret: 0775f692bf829871ed2387acd1f53540d3dc73ac2fc58e98ffd51129ffa64e00
b7925096d67ae189f6562bfb529906f3f68ec757aa07584c3792d1111f6160d1
key: 70764752b2169ae639d76384b24509bc
nonce: 14287d3b765b1df4193a1b5e
exporter_secret: b02ad0b1be828074bd3fe48a02223b82708ccedeb548212675fa951
2abb81f8848e53cda8a7b535107d59ae87cf4d8dad5a8de609aa65f00a482313de47d26e
c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 14287d3b765b1df4193a1b5e
ciphertext: 9d4a1550534af1328df8099a74afde1231e6f3c09ed1a74c93f127f88932
944b9b6e492170f47ab316e0712b86

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 14287d3b765b1df4193a1b5f
ciphertext: e006f16189ec590e6e0b103be2902960e073a7502acb4590eed9878173e4
1f695de6d5ca175e442148bb1abba9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 14287d3b765b1df4193a1b5c
ciphertext: 85a69bfcb65d97acdefbadaf53ba4997747821963c2144b7622fea6bff1e
b88651f725b491c8956e21d6de8c3f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 14287d3b765b1df4193a1b5a
ciphertext: 4599b87a939bc8e1fdcbdff0bd02a638dc3efba88245c5fbd76c484881ac
e6099ac25e7a2aeb7eff764d2a5fef

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: bd427ec7e3dcd35dcb2f8f377e3f989ef1d3c85274c360e211a4ef4ee8099f40
seedR: 214c25c1dbb0f4e9210f118be3fe776f418d8c71321fd52b3c0b9037061ae00e
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0412cc8b9760a97a5b672c0ecb2fe2795faf145c6f0836b86687bbd242cbe99ad9a
f9399a389d2fdc383788f226b249d41d5dc37d9d513007c8a8a39f4d3d842ae
shared_secret:
2fa25f0eb9460068c2f56cd59513191dcaecae30872277c3d90f5bcf0b2d1862
key_schedule_context: 0139f6011ebbfa0b089f98c9db37956a61abf9fb58427f56ad
a80743584c1a6cdcfbd55ffd4399433c54b22f53e40738082c9489846c4c19c08fa771b0
388da3eb8c9942e377e9f72fa4152c161bfba6c407fe5ee3d6517b56634fdf07ade5b4fc
b1358e1f01175ac61ef5c191ba765599e625e92cd4623fea16bbe3a0ca2db1df
secret: d0adc9e2d51fb752963eea463088a5eac455a03363c2d63174945ee7b0cb9b56
3cd1e50dcddcf74a2f2d8f722e9118b4625de1f56cb579a33dfffa1952b2fabc
key: 4757481aa90b36cf418939901246faf7
nonce: ab650f6b6082541bdf05fd65
exporter_secret: 00e5a1f4629ab6ce962fe771041a06eb1bfda745ca39d39a69eafb4
cc93a0a9cdc640cb701eff49ce51407034c16acf02c4dd4a1404a5eb7ab6e97713d76adc
5
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ab650f6b6082541bdf05fd65
ciphertext: 31c0305ce0f315773dbfab962f552e4dbc85f2617c03d6908e1728f2088f
d28f9441c3dd60aabb9db906034083

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ab650f6b6082541bdf05fd64
ciphertext: 064f2bdd847bad326e735480c1c398e3874b86d98e377a017b79d88909e6
1f0aa7b16e40310dad83a8ce8cedc8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ab650f6b6082541bdf05fd67
ciphertext: 5195de860f0dab84fec319733df47f344017cdcc516906f82f6039f61733
bc763a9910a28f7e6ac1bb85ffc13c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ab650f6b6082541bdf05fd61
ciphertext: 32e37c69a3ab922dba82a11d6ea97247321621d14bdf7d050ebe3d2b3b83
ed2e4bfefc4ec5cb7016f2030400fe

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: cea4bf4dccff45e6b32759ffd725b14fa714981f0a455749eb378c350c6f4a80
seedR: 703e8848a914907771dfcebf71aba72c36f934f27b00b6b1b6fd5e7d1c8c4b91
seedS: 69507b25e67c802d6f278bcd681ee57a78f5ece184ea88f434d604f140f9328f
enc: 043cdcd5809e4fec0a4701d4c5329b6a300552a583172064179c3cbd10899d9f4ab
379a3f3cfdf7191d00a969a973b2b8592027c13cbb9b9f8738341a379c658cf
shared_secret:
6bb9bfb0f0334a9a394598236f474253c9fdddc13e84a8361443a029e3ac6689
key_schedule_context: 0259a145bcce1c1c862714bcd04c342351f917429e57578e3a
2fa684c7ed0403ba264455f90835145bd18f39bfadab2d3808163e74fc91c733021e758f
5b70c2668c9942e377e9f72fa4152c161bfba6c407fe5ee3d6517b56634fdf07ade5b4fc
b1358e1f01175ac61ef5c191ba765599e625e92cd4623fea16bbe3a0ca2db1df
secret: 42cfc6c381847cf6ea064d94358c8a6907c22f58a615b2adc8c8598c27e9c02a
a8672874c6bdabfc64a72b9c4761824e24a09708d673cb9460ac9fe92ee89461
key: dd67821955121c4915b0be5c732534fe
nonce: 0c7c7f575a7b277715ca9612
exporter_secret: 2648ec923fd2d78c454e36d8425e0d5ef29db0d754cedbbd3529bb0
be3e84cdd3114f2c46c104370b1bb27eec6604f9abfc23b80d27f879c6b943b936408e4f
9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 0c7c7f575a7b277715ca9612
ciphertext: 4cf3d83567d6a232c1fcabcf4ffad14b99dc52dc6edae225488eea91c991
72160cebf441cded2cadf27e3390ee

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 0c7c7f575a7b277715ca9613
ciphertext: f4ac648b02822cf2888b2d2593d07bb65a7ac3f9a23bfc0602402bbcdea6
0d66680669d9bdbd766499a26dcea5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 0c7c7f575a7b277715ca9610
ciphertext: b461884662a1a06efa64a9371b6927151c4b09ef52a1722e3471491d7e97
bb59634fe02df872f006dfb73c9bac

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 0c7c7f575a7b277715ca9616
ciphertext: 929f0adc290c89e6d6ec1940c46b17aa4b8025a2f57fce800e67cc419a94
198414f5fa0d54ea42efd72b522140

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 8430ef4fc3232e1174b3d9e7855ef99cf20efca45547d4ba8cb58d452a8fb169
seedR: 2e15dcebd9e5817f69c33329a3c95327782b56bae40b0c339143caccb1f4b6c0
seedS: 7aa6315fa003a4e3c240739b6a23612288ff95433b15369ec76709401997d9a1
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 048da2b0b7c8fb2a9ebb8cd697429d2767ca5233676b0b9a6fc6c8e7153bcd49ec1
5094b3f2a91f09d143234a7864a84400bb7bab2c3de01dabbbc76543b90e692
shared_secret:
e2e24477a852dfa09419ef02424daba0a51c200631c248947301f859cd22920b
key_schedule_context: 0339f6011ebbfa0b089f98c9db37956a61abf9fb58427f56ad
a80743584c1a6cdcfbd55ffd4399433c54b22f53e40738082c9489846c4c19c08fa771b0
388da3eb8c9942e377e9f72fa4152c161bfba6c407fe5ee3d6517b56634fdf07ade5b4fc
b1358e1f01175ac61ef5c191ba765599e625e92cd4623fea16bbe3a0ca2db1df
secret: eac0d8e8f50ff79803753a1d6306fb303773defb1624467acf9c711bf35f4a95
3535dd94075a18e65526a492493c8e641e69f9b185b29504abd7f657fa7afaed
key: addc7c894686a178a3d3d0314cc54f9d
nonce: f2a7409f2769e87feff57310
exporter_secret: 597b16d322451c9697cff03410a96f296904151bcffa9b375627d18
49bf32144eee1e96573de5f8a298657cd7932b35ff4f8d55b7da061c2ba61c4a2cf9cafd
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f2a7409f2769e87feff57310
ciphertext: acab9819f89feb79f15c2c32b82c4393d0bd034edc0c71b92ae0d70fff25
a91197ec61351a9d389955321ce309

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f2a7409f2769e87feff57311
ciphertext: 060524942f667d185c593282bc22afdaaffd77044d223c2f96335635b6d1
c5fda42a05c58dcd24f2c2a93d5c54

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f2a7409f2769e87feff57312
ciphertext: b98699f3145191c942bfb13de92402dae2d3f8b635fb822a2d4c1f4322df
8fe143f65979e9b0eaadb52e06f63d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f2a7409f2769e87feff57314
ciphertext: 493e8d78b97f4d8ac411b55080c47e20faba6cf504c2ae5f167415c3e592
2256529eddc156c82fc1ba5eb0a9be

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: f966c1df886cd83a97441aba1d06b92836085ca7da14093afec12b550c5bc743
seedR: 945a0aaac9993ea16b9799f37660fb1bcc9daeb478b24f93c6fe9d28f4e43648
enc: 04f9def4c2a79ad0de56c07c51b2685e4b11dd3064352b5cce1c8460b5792f6f3ef
5f5feef0ad3f2afa1c2d0936df9fb1de5f0a3e18ea9dc397e9731212208688f
shared_secret:
d3d549912a1e5c022a263645f5b1c3dce5cdf29d8dc069a43df671056608db02
key_schedule_context: 005193809f9701d761ad3e980ec406cc14ea789817d821d0cb
139989260f37f4c6d3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: de57f473b03fa4712e275ac1155df40b37a5b7ec91d023c45d6385a285afcd5c
key: 2bf084674f1cacdad7b7eaf091569d223e58506074e67b1b19b4d73f442cfe92
nonce: e807351ea0ef4dbb3a5a7282
exporter_secret:
0fe0e769d30bdff5f70f257f6a8ff3ef19efd7d3ff8d1998bf245c9171007b67
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e807351ea0ef4dbb3a5a7282
ciphertext: 116161f91935ee694599475fdebbae25c9cdaf1556b0c36a2147b2ec6dd7
44b6cca21653d6eba19aa18497527e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e807351ea0ef4dbb3a5a7283
ciphertext: fc9e37e02223a0a36d81674d6a35ebdf02b3e04380b96258d760efdfca3e
22944b39eb4251b768d2f263702c7d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e807351ea0ef4dbb3a5a7280
ciphertext: 1a4bc5c2d8fee8e95aa8467de986c2863f6cc2151ac260746e748da54aec
663066383b2fdd8bff239ae5ffcfbb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e807351ea0ef4dbb3a5a7286
ciphertext: f5c3e90ba95dc013d4adc127fe3ffc6f716d5c11b2b0b0b7b77ddf2a3edd
ac7300f335093de498f1b06a2a7217

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: b8ed4f2d3848131574565d7b064ef6af11ae8e785f061740ccac427454210a99
seedR: 0174ff8ed2b9e11fbdaf886385c52414f2c9f12dc0368c7ec4758842924204ab
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 049ff752dd489f76d291a3963cf6794e01b5bf20e42108eff5aee09420aaf0ece63
4474ccfe157bb6278d768616a876ad071198362422435d3b83e50714d10cc04
shared_secret:
23bf73ace50b82a0bdefa3566bead941b906b4d21e8a8a2717c038313f337da1
key_schedule_context: 017d40471421306b100f7401fbf733fef208e1508bd2744517
e95ef7471f21a1dad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: da1fcec944cb76dd0456f1eb1eaa53bff623ab29b170f40246d97d40364fafef
key: f93784390a6dce110c42f8aa2a693c5b04c8832904c56f463213933aac38a0dc
nonce: 792160de69224fbea47d0f58
exporter_secret:
11e63eb36821f1660b16da3bb62970a8282fca708e536572b29385c22592fc2f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 792160de69224fbea47d0f58
ciphertext: 189cbcdbb3ffed4f1b9ac39c1489f166c2a81a761fcec425417796bc668b
1a9880bdf3071bf9fc035cf475094c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 792160de69224fbea47d0f59
ciphertext: 1aa366e69572430fdae76123d52807ed604115d93924e52f3d476a0f9b5c
9b72fdc0cb7e9a2de0134a9f42d4eb

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 792160de69224fbea47d0f5a
ciphertext: 992949d7e750036b6efb8f5fe69a0e3c603455ca45c9257c5bf7b46e495c
b507b3a0c7fc3e71585bbc8821d485

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 792160de69224fbea47d0f5c
ciphertext: de8353422139b40c790560d48a0c4a88d776f1032d47e10a982ced7304a4
7b0441c72e15359e1b01448bb13a9e

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 7caefb74979265b42ddcaf631dd91063ea133288deb0727b975772ec87e1da6f
seedR: 461ad16378c2f33737cf5e2647130bd3d95884084339b3cad988c24344765614
seedS: c3bbf40bbdcac362f229f42e10655e596bfb196d6b41202cdc72f05985a34112
enc: 04a5a350253f52e8beb1bf84fffdbc8f21638f2b712c7cffbd9c13024ff4a78ce10
24fda9816e7f15b26ef2e829ad837ce309191b57884235323579e83238e6a14
shared_secret:
c6aafdc9bedb1059de752c2eba636b12ce862dcdc8d66cdc3db22747ca9ed421
key_schedule_context: 025193809f9701d761ad3e980ec406cc14ea789817d821d0cb
139989260f37f4c6d3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 9e403ec9b2469ada2d329600a0d5948c9da7e64fe84d41107db57b3f281d24ea
key: 7aa2323000369c3ea4c42a541166842257a356873a736175c8e2f544c35ccbda
nonce: b2748fac7af9e804ae7782ba
exporter_secret:
4a9a4d2668d24ff58e8cb5f6a433f17c287950d64acfb68ccc3c543c03207ac2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b2748fac7af9e804ae7782ba
ciphertext: 432e85207001a2740faf86e8af2993fcc3bb71addd5deb99c85380ec4b99
6587c39c89c9dd816e04fb1aa794d1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b2748fac7af9e804ae7782bb
ciphertext: d9824a087c2242660e7611e019be4fa863cee259302e12c4f675e69b3cde
f2dcfff95820410569387f20288363

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b2748fac7af9e804ae7782b8
ciphertext: ddb51e1738542ad3b3c9c044bd8065084f0a18090bd5cc84677b77d6b2d5
2f0b0fb835a324038458949d93c7bb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b2748fac7af9e804ae7782be
ciphertext: e163722af36e885fa4c1e5b50ab7d07999ec24cb2ee6d3991508f620f1e0
2a220cdfa7e7050e1ec0dd57903cae

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 21f704bc7e91e86ff847c92256eff72055cefa2a71b571ee685027df24ee62a9
seedR: e240e9245f55bf7586839b8459a558847e4aea085eb998b074d9b69578049815
seedS: 3e1919f06df7acae525268b20f903dbf0c28463dfe03a45b9963b514971551c4
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 045767c831521d698762123e15270505d69a39c59e20dbb5356645a471158bc44b7
e12cf90d42d681dd99d1fc5ba9b79bc09533dfd37ed8b6abff1f23b0db33a3f
shared_secret:
cbb7deca491e883c25e61758c0eb763d54c7fb226ad5fcf2e8bfdbb3fab8a2c9
key_schedule_context: 037d40471421306b100f7401fbf733fef208e1508bd2744517
e95ef7471f21a1dad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 637a33e473fc14aaa46a486b1b695f6067660bcc6fd3e2862142d1df0b48b08e
key: 6115b6bc65f988ecd63992d003eaab1ab07d090f28389721b0d5d7b6e32ff061
nonce: 075b940e8cc3deab22697437
exporter_secret:
64aad3a4115be168e7ce37549f547c54d9e4129ae73e52b96794387fbd105ab3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 075b940e8cc3deab22697437
ciphertext: 2fab5b74e4d1068d3f144e2d7c59a7f341c14285ef81d06eb52e43bfef31
8e6746c5e730bdb76e70efcad64895

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 075b940e8cc3deab22697436
ciphertext: 2a540fd8818d2fb1552d4f0f79bcea000978e897f223b0daa6bfa7098ee2
28384b38d6f92e2c1c0a5a7e457936

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 075b940e8cc3deab22697435
ciphertext: aada50b571228e2f68f0cd8278698520f093570e9a3634a303a91f16196f
dea76c492b1b7742717bfbd02aab7c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 075b940e8cc3deab22697433
ciphertext: 038f3c92492a195f583773800b41de844e243f09ebe4da957903bda60ccc
688a8f29189b6c67d6603ab39e818f

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 0bb5c77579f005bdc8546b88b7cc679980e201ae8bc34b2be736a8db03dfbd790
fcdc9edfa4d4c5e6a96709d42eca006c9b53caa1a55601abf711433d0b8fdda62e9
seedR: db22a4c066b61599ad4d991cc18c64bd1a04c14d2efb242a71668759408920706
28455f775767b1d40a664ad9843a0c84b60897b143cdfc9856da45adbda7162e037
enc: 0400a729d8078a06e9cd9b11ebad239de44695b605b558bb3a2c8bdd221c09a95dc
1a62207c3d0e915077030dffa9a844d3bc27e0f2dd3e39440a5fa9eeb3da2d217de010a3
c7c4513be72801d6edbfc0667bdc2ccb59c3842ca36dc2b66e5717d6d2e7f32736738ee5
1dcf04d2cb8b61772185be576d658d374fd12db956404a05c688408
shared_secret: cba1c89156985960c7499f1278b990e7dcb4d0f11961f4f6b5d11e34f
eb60645b02951fc7899005b9004f8717cb613d182e1282d85a630afee35d4069a98dc8b
key_schedule_context: 005c0b2bdbbffbea1af82c95fa5560defe4ba0a05fd3c301cd
fab3bbc2fba9783d13d14ecba2cdc7a7c1f544087eb5b3a22ca199e34879b2bbeab3d644
cb2a005dd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: 82f1879fb4cad901723db6e2c4d6b5290177cf3f6bf58254b4d44eb4c68a9a66
2a9c1f3d78b3c6d58d7bba59433d0e0840e8abe7e2814ac4f35959866abc4908
key: 99559cf52ab53b1be7eb8a5b9a96ff1d3b13bf7a427c954dd121d1c0297535af
nonce: f57438d2eb18ea2e43dfff34
exporter_secret: 856d144cc0ff0e5083667c6e4474c1c0a8b06ce1e69ee714bf8fc61
edaaedf81c11066796dd24abc57e11f95ba1814936ccc193ec31f588a0200dfa3c2bc29d
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f57438d2eb18ea2e43dfff34
ciphertext: 8ac8aceb94aaafe04e377f02781a5886adfbd58cdfa47c8854e46f838c41
251f8db163e8df49cd34c2359de332

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f57438d2eb18ea2e43dfff35
ciphertext: 71730e04bb7563f9abae9a396bbc44cac27785299ba89c39804618d11069
f478ffa32d1051d17fbde51172ee67

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f57438d2eb18ea2e43dfff36
ciphertext: a2a27310660319f03e221044d846d7463ec20e2bec632cae94d6051980fc
7f9e77769f8ab79e5657ae509ed9eb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f57438d2eb18ea2e43dfff30
ciphertext: 600d5c908ee632006341a4e8b18f2543ca6adb3c6b4d3efb4d94b1a21a06
9c8e9108c6caf9a5f947b288e12bdf

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9c1cf1a41724bc22b633f782925abc88a73cb388de1c4e54b4c468a537b95f528
cd4146819d389466f46194d780675216755df0934a4209dfd6bfaa0d4161c8730ef
seedR: adcd07f4324ec7b59a48feb69ca15c3124510a44b7cca7cf54e1e4ec8dc364c28
58e2c470b94cc0a00fc7f5aba75aace5c3e4c64056a4da84ca573ae5f644d08c58c
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0401fd0d566d92fbcedb74a69d5c3b950259a7d2b215e5a5e7d02e104f7eaed7e24
6baef934a445e075fa1e2dd7553546ae964a5b0dc9912da672d3a1320052882854601120
3cf1e92f8c98ad45fbe8f55f29009931c0bed343c03d63ebef4165993f24d1480643758a
2232b66aa709460937b01004d111db80ddbdd177886d5dc306b9bde
shared_secret: b34a2d40884effa01c421289bcaffb7167ccdd08d091e9611e320707e
678a1b920d367e13c74135f462a0235bc8d0afba4a8a799259102602f7073626ebb6ac9
key_schedule_context: 017344e204124da2a856fc5693999bbfd1242c27f4b2f16fdc
92751d458fbb606adde7aecc32db4dd5b0fdbea7655c7c0e8363da1a34370ba59bfdb421
08a4bebbd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: c2859ff126ff51ba4f29a144da23de9cc04308966d4abfc64ea61ba9b92d97f0
2f948524a9b77c8924f9b76386f2f32032003035627b1d841f681938d7c2b790
key: b3a4ef10ba66c3e44c70cbc0859e190c92fde7c6be10c7520c6584c8407958dc
nonce: 1f3e4b9a495a795f36a2c31b
exporter_secret: 118f58b4b744a81ad62d5cf34a2c731a9b1a9463493874367128964
c138f69564e0d24be5644d37c0be0fb4bb7972695d7522d7a8f7cd1011d26a06432659e2
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1f3e4b9a495a795f36a2c31b
ciphertext: bd4cb682ab56c38bd78a636ac76b7d055a18f35e6d2c175f4a924a12b376
b2d51f804d505d95c9de431136e260

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1f3e4b9a495a795f36a2c31a
ciphertext: de78f98a2ad7ebef25823547a7c4c35f48f4199ab3ac1181885e9c34fbf4
02bc5b4f00e7deef78e406ff5666ad

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1f3e4b9a495a795f36a2c319
ciphertext: 7e5c569d5d5f9b1b45f43fb44eeaa72ef49cf6b2aebc28ca2f4078400a57
5450eb0995fef2c06aab721f3b5a70

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1f3e4b9a495a795f36a2c31f
ciphertext: e75aef6bcb0587c8a9b13c6e7a05534e41cc48b80513419cf0c1cade3dcf
6ec34b1c347b3e8cd1b4c0df55b63c

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: b8623a6c6e57b51151aca1916dd6f8290e9501486cdb360f134da7ec3a57ab5fd
fa6726009c1e80bdcecb12ce3a3358d16b51ae117b89510ead6024126bff29b5b5c
seedR: 7041e8e73ace4154eeff950aa68a34f7d644c085bebf80e6f9dc5f91297bc0f6b
7c1613497505acfb2f7bfc20c235d8f6e6b3c99a9bd480298e60dac38915b779de9
seedS: 0a00417a70272b0a5c39e39c2537d8d1b89cbbfd9774353d5214b1e0745692053
1e2f6a11298d097ba2e60ed0f3ec91ba5ffc2b090ab4abd9d93cb91bca635679606
enc: 040163a2e864eed7b69a545f0eca7f5b5ff90e9d6519026b5ae7a779686b480b245
344b9ac678ce09b5fbe9b50eb720ccab43a96f39ddb3dfe379c852c1c155f66037b010fa
5847121600b64681161cbcdd7092262bbd41458b1e4238cebe812385c72716573dfe1d15
f28966802970e854746ecc566893311658ac80dd3e48160baa4bd35
shared_secret: 2ebe01ca8ecfcff72ff75d020fbf8bd293de16ce5344e8104f6d7b5e4
6e490a67357d634ed1b799e318d43a6f00e33bb47ba7f4369db2cf7934c31ccb382fc48
key_schedule_context: 025c0b2bdbbffbea1af82c95fa5560defe4ba0a05fd3c301cd
fab3bbc2fba9783d13d14ecba2cdc7a7c1f544087eb5b3a22ca199e34879b2bbeab3d644
cb2a005dd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: a3208177cd9a0e7aa4b5e5fcdd33bc77a013a63393d171a41af96302a0df3a7d
83c74e610ddd63bbcba1635b1dfb2b08511fdad08af54069b72ed67747500eb0
key: 1ef22ea092c9ccccc47a766cfa948853560ec6227d184b96dc774580cff7d493
nonce: e6839e5eac0ff2ccf83b043b
exporter_secret: 8fb971bb022801c790a0e606ca103bdc9ed730112dc938ab40be324
7f6dff011da142b59016c195108a97176d43e9cadb80b74b80b42bbb0ab9c34fc49a2e10
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e6839e5eac0ff2ccf83b043b
ciphertext: bf894099413caab439838b774b9c45ba8409e66038e94b4ce5930e6c8e57
cf21be7038259de6fa5bd39ae19d3e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e6839e5eac0ff2ccf83b043a
ciphertext: 96ddf44397255849539b4ed31b7bcdcbee8f3860af162a1439f5fa9798af
585505bbe8a734b3767de2e7596e7d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e6839e5eac0ff2ccf83b0439
ciphertext: 2ee3e337c261ca2e9afa25d3850ab3a9dcce35f1f7c29052971cdd7fdf8f
eaca319fd8d55a95f34cae744635a0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e6839e5eac0ff2ccf83b043f
ciphertext: 28b5d90cae62c6aa3b314501d297dd57aac50245e37620b892d1004827d9
597aab8c073574cf47434e7811dcb7

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 587e4cd7d645885cc34c50ad119960e34f67a309e70202e9df3d63eac1a21d85f
2ba2b98d91391a2571e3acc9a116e9af1f6e487d6e15cd954ea254738783d880966
seedR: 592ffb083b5c6298c965eb5fe6b83883be0f6a4788710d2cffc653bf77d44cc89
afb26778caeeb7b308ae2e9fee5da0f797ccfcbb5c28ed9e7f3a623c852f276e878
seedS: 0ac7111a27b04209f4d0da0be3893b2a85b5bb7e80999e0d39d9f0bef977525cc
1c9af527f5f032b30daa2ce956798198c88b8b2d44d014e62225f82777e8e9c1ca9
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0400c1de46a40a152a77461aae4fc2e109e22b4787405d025c9b0923bb0c050d454
ee48f906829b10decbce00f5ec8120a96626947a69d6e44ffe42fd07affeacc4fcb00cdb
66d02d1923286a62cf8ebeee1351de8ba4873f52413572e4f830eacdf62ced144b9c7bc2
36403c209822d897c8449c5879f70e4e5b2087365e790716eb2baf2
shared_secret: c4b7a3d04f08eecbf2e8db4fdd4ae58407c003c1f5b1133f0678a5a87
d694315de3d17426e1bdf3a986953ecddf214e520aad9461e31dd6e4f45e2697bfe6851
key_schedule_context: 037344e204124da2a856fc5693999bbfd1242c27f4b2f16fdc
92751d458fbb606adde7aecc32db4dd5b0fdbea7655c7c0e8363da1a34370ba59bfdb421
08a4bebbd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: be6f06e3c59500fc9b275b56a7b93845b0010454b7ea9ea950c5f0b3d916b2e3
5dfc5bde370c9bc5d98964a40300aa845c87c7cedc2fdfad90a5d8dd67aa1bcf
key: 0600853c06676fa3548383022f0b1efe82c5fcab930a6d209a27b9655d1bd16e
nonce: 096508857aa1d34f5d80dca1
exporter_secret: ec24d4fc5dcd8d3e98309dc74cf26b3c043362717689ee2911a90b8
bb68a04a868fcfd72f7c937a6f52b4abb4fed5aebdca5934932ef52e70badda75305a7f3
8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 096508857aa1d34f5d80dca1
ciphertext: 192c1f34a6830ed1a912ed1a4c967ed70c9dd75dff2ec9f64b9874aa8d1a
7726e1ef01bc40f7033e9eccfd2c8a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 096508857aa1d34f5d80dca0
ciphertext: aebf68cf345d94817666cfadc54cb09f230c40f9924a0c0d2c38fa0c5c96
d590633e5f79946848b6cef39b4a56

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 096508857aa1d34f5d80dca3
ciphertext: eccf58d3b7a2011479a68db3eae1a2fca04d915bc42335597293db204099
cf6ce7662dbfd9ef1d48459405cd49

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 096508857aa1d34f5d80dca5
ciphertext: ae044d0317abd2c60047f699fa1746cb47e17fd369bba82b11d9ff9fed96
aceaf24f49b79de5e55428f163287c

~~~
