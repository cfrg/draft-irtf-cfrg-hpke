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

  UKS: DOI.10.1007/BF00124891

  TestVectors:
    title: "HPKE Test Vectors"
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/0e9e02edb01e2ef6cfae7fedb52f436538328c2c/test-vectors.json
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
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - `GenerateKeyPair()`: Generate a key pair `(skX, pkX)`
  - `DeriveKeyPair(ikm)`: Derive a key pair `(skX, pkX)` from the byte string `ikm`,
    where `ikm` SHOULD have at least `Nsk` bytes of entropy (see
    {{derive-key-pair}} for discussion)
  - `Serialize(pk)`: Produce a byte string of length `Npk` encoding the
    public key `pk`
  - `Deserialize(enc)`: Parse the byte string `enc` of length `Npk` to recover a
    public key (note: this function can raise an error upon `enc` deserialization failure)
  - `Encap(pk)`: Generate an ephemeral, fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to `pk`
  - `Decap(enc, sk)`: Use the private key `sk` to recover the ephemeral
    symmetric key (the KEM shared secret) from its encapsulated representation `enc`
  - `AuthEncap(pkR, skS)` (optional): Same as `Encap()`, and the outputs
    encode an assurance that the KEM shared secret key was generated by the
    holder of the private key `skS`
  - `AuthDecap(skR, pkS)` (optional): Same as `Decap()`, and the recipient
    is assured that the KEM shared secret was generated by the holder of
    the private key `skS`
  - `Nzz`: The length in bytes of a KEM shared secret produced by this KEM
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
    `nonce`, yielding ciphertext and tag `ct` (note: this function
     can raise a `NonceOverflowError` upon failure)
  - `Open(key, nonce, aad, ct)`: Decrypt ciphertext and tag `ct` using
    associated data `aad` with symmetric key `key` and nonce `nonce`,
    returning plaintext message `pt` (note: this function can raise an
    `OpenError` or `NonceOverflowError` upon failure)
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
- `DH(sk, pk)`: Perform a non-interactive DH exchange using the
  private key `sk` and public key `pk` to produce a Diffie-Hellman
  shared secret of length `Ndh`
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
  zz = LabeledExpand(eae_prk, "zz", kem_context, Nzz)
  return zz

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  kem_context = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kem_context)
  return zz, enc

def Decap(enc, skR):
  pkE = Deserialize(enc)
  dh = DH(skR, pkE)

  pkRm = Serialize(pk(skR))
  kem_context = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kem_context)
  return zz

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  pkSm = Serialize(pk(skS))
  kem_context = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kem_context)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = Deserialize(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Serialize(pk(skR))
  pkSm = Serialize(pkS)
  kem_context = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kem_context)
  return zz
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

For the variants of DHKEM defined in this document, the size `Ndh` of the
Diffie-Hellman shared secret is equal to `Npk`, and the size `Nzz` of the
KEM shared secret is equal to the output length of the hash function
underlying the KDF.

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
* `zz` - A KEM shared secret generated for this transaction
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
key, and the entity that used the KEM to generate `zz` and `enc`.

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

def KeySchedule(mode, zz, info, psk, psk_id):
  VerifyPSKInputs(mode, psk, psk_id)

  psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  info_hash = LabeledExtract("", "info_hash", info)
  key_schedule_context = concat(mode, psk_id_hash, info_hash)

  psk_hash = LabeledExtract("", "psk_hash", psk)

  secret = LabeledExtract(psk_hash, "secret", zz)

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
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, zz, info, default_psk, default_psk_id)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, zz, info, default_psk, default_psk_id)
~~~~~

### Authentication using a Pre-Shared Key {#mode-psk}

This variant extends the base mechanism by allowing the recipient to
authenticate that the sender possessed a given PSK. The PSK also
improves confidentiality guarantees in certain adversary models, as
described in more detail in {{sec-properties}}. We assume that both
parties have been provisioned with both the PSK value `psk` and another
byte string `psk_id` that is used to identify which PSK should be used.

The primary difference from the base case is that the PSK and PSK ID values
are used as `ikm` inputs to the KDF (instead of using the empty string)

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

~~~~~
def SetupPSKS(pkR, info, psk, psk_id):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_psk, zz, info, psk, psk_id)

def SetupPSKR(enc, skR, info, psk, psk_id):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, zz, info, psk, psk_id)
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
any other identity.  If an application wishes to authenticate some
other identity for the sender (e.g., an email address or domain
name), then this identity should be included in the `info` parameter
to avoid identity mis-binding issues {{UKS}}.

~~~~~
def SetupAuthS(pkR, info, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth, zz, info, default_psk, default_psk_id)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, zz, info, default_psk, default_psk_id)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, zz, info, psk, psk_id)

def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, zz, info, psk, psk_id)
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

HPKE provides a interface for exporting secrets from the encryption `Context`, similar
to the TLS 1.3 exporter interface (See {{?RFC8446}}, Section 7.5). This interface takes as
input a context string `exporter_context` and desired length `L` (in bytes), and produces
a secret derived from the internal exporter secret using the corresponding KDF Expand
function. For the KDFs defined in this specification, `L` has a maximum value of
`255*Nh`. Future specifications which define new KDFs MUST specify a bound for `L`.

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

| Value  | KEM                        | Nzz  | Nenc | Npk | Nsk | Reference                    |
|:-------|:---------------------------|:-----|:-----|:----|:----|:-----------------------------|
| 0x0000 | (reserved)                 | N/A  | N/A  | N/A | N/A | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)  | 32   | 65   | 65  | 32  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)  | 48   | 97   | 97  | 48  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)  | 64   | 133  | 133 | 66  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(X25519, HKDF-SHA256) | 32   | 32   | 32  | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64   | 56   | 56  | 56  | {{?RFC7748}}, {{?RFC5869}}   |

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
| psk_id            | 2^{61} - 93  | 2^{125} - 157 | 2^{125} - 157 |
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

* Message secrecy: Privacy of the sender's messages, i.e., IND-CCA2
  security
* Export key secrecy: Indistinguishability of each export
  secret from a uniformly random bitstring of equal length
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
essentially the same form described here is IND-CCA2-secure as long as
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
- `Extract()` and `Expand()` (in DHKEM): `Extract()` is indifferentiable from a
  random oracle. `Expand()` is a pseudorandom function, wherein the first
  argument is the key.
- `Extract()` and `Expand()` (elsewhere): `Extract()` is indifferentiable from a
  random oracle. `Expand()` is a pseudorandom function, wherein the first
  argument is the key.

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
means that a property does not apply for the given mode, whereas X means
the given mode satisfies the property.

| Variant | Message Sec. | Export Sec. | Sender Auth. |
|:--------|:------------:|:-----------:|:------------:|
| Base    | X            | X           | N/A          |
| PSK     | X            | X           | X            |
| Auth    | X            | X           | X            |
| AuthPSK | X            | X           | X            |

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

In the PSK and AuthPSK modes, the PSK SHOULD be of length `Nh` bytes or
longer, and SHOULD have `Nh` bytes of entropy or more. Using a PSK shorter
than `Nh` bytes is permitted. A PSK that is longer than `Nh` bytes or that
has more than `Nh` bytes of entropy, respectively, does not increase the
security level of HPKE, because the extraction step involving the PSK
only outputs `Nh` bytes.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see {{?RFC5869}}. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret `zz`
and has access to an oracle that allows to distinguish between a good
and a wrong PSK, it can perform a dictionary attack on the PSK. This
oracle can be the decryption operation on a captured HPKE ciphertext or
any other recipient behavior which is observably different when using a
wrong PSK. The adversary knows the KEM shared secret `zz` if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

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

* Forward secrecy - HPKE ciphertexts are not forward-secure. In Base and
  Auth modes, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In PSK and AuthPSK modes, a given
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
seedE: 8745a0f6b41d4c3d4e3711de22cdc39a432cea8d4848c4fb0a61f408d65383ef
seedR: c7514a77820478960bce752b13c8a52bf47d659dc2a9afceadc8c2a90a878264
enc: 55f84bafa12ab421fb9ba1a17b92bc14e6af760fe82975ff7a7f4ad74f5aee72
zz: 6ef5922567d2c35c46fc27c1a129eff64b446f3b9b2b599caba56da008fac7cd
key_schedule_context: 00a2421c47ebe6a1af67852ed227c2cb435b870d44c5cc78ca
48acff40cbb19bc844c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: d1b44fb5bc0383ead9ddf656fc24a882085a5539e637fbf212b6081208e784ff
key: 40bcc4450683f7808f7e76ed1c884526
nonce: 89929424029ca4a50476f1b4
exporter_secret:
0999fc89102b483e4cb63d76ba799deaf419169a9c145d42f7c96d05134cb7a8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 89929424029ca4a50476f1b4
ciphertext: f37ba3947f9b07453e3e5ccd488d846b59100b5dfeaf6ae99073903fd6da
32428c0d6101edc52ce236583ef641

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 89929424029ca4a50476f1b5
ciphertext: 49710c794177a0ae941dd351db77402ac22128f45149ad5f9ef78d85dc89
63ca0036f19e4331512dc5a7555122

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 89929424029ca4a50476f1b6
ciphertext: 422523c6088fe42b1bf88ca265fac62699d5d5a4303efe95d90e92ca3f3d
26e96ccfc8608e73ef947fae409e34

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 89929424029ca4a50476f1b0
ciphertext: 4ec67190e9fe34664c78cb894462f295dfb3e2fa8f7a1cf07a3c4a734639
eb0828a7421c64f062e1b25c9e0b83

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: c9fac914dcd6c8a3be7b75681c67cfa6be349820e8a6bb1804d2166841a2bbb0
seedR: 81c60c0615cc3a17328d703f0b7adb13f7858194f0e40d876adebafdd159f5e9
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 2e32c62cb61a6f69a2a905a4fae9e5c273a44e01f844d6490b8e45262062832a
zz: bd485dc56079654cb2f56006a6688fb0b568e55f95fe0026641e33f3b622457c
key_schedule_context: 01f979af8f01981d30dc4dd8856fdb2f2cdc71ca4c38a64d1c
e95bb190bd8265ed44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 80c9fabceec3c41458c07b8c3ee2b375732bd2f7a3b6122294c1a372ba664e94
key: b58a1b48da0c4ae82dac2c6dec5c35c5
nonce: 63fc8b0c10267da06700af9f
exporter_secret:
2f6d64cfad2ec79cad64ae7bab97f78cc169a7bd724fc84ae594b1e06985ae04
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 63fc8b0c10267da06700af9f
ciphertext: eb5bab8fa59022ff72e30cb7bb3447e40d8c50c46d30e58de2069a44736f
5d2e7464d50c3610341895c40dd91e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 63fc8b0c10267da06700af9e
ciphertext: 42ebaf8c97eb8d7727a20c094a021ae904e86341d2c7cf1354a99af9452d
c4bdb277c7316464915614158b3f7d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 63fc8b0c10267da06700af9d
ciphertext: e95655857d0dfc355b75978a6b0b63001ae513f8df38e7142b1ac4447a24
00307c741316fd4dc328da387596a8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 63fc8b0c10267da06700af9b
ciphertext: d193028b661fe427d34c3b14c1880feb8fe51a573b4155e1b5d872c324e6
731aad15262ed1c5f76c0c0fabca8d

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: a414214a0b29b84a65d7822dbe1011ff93324d5ce036826525eb536bc82c01f1
seedR: 7c6ac4d01c9915d3d9ecfd6e08642ddea42b7a6db427ca3a2fccd0d9e8f61ad1
seedS: 5ec7181a2eb57db5a0838d9e89815c23a069a1ae5059bce5a5d4a14ea56f3afe
enc: 495b9232ba57496a9d160503ad0c0356e0ed84f3b8e6e1d774b5f09cb39a0f66
zz: fb685f676bb56e5599b6ad5791accc155f812cc23a971f712f2590d7345fe8c7
key_schedule_context: 02a2421c47ebe6a1af67852ed227c2cb435b870d44c5cc78ca
48acff40cbb19bc844c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: ac8ddb828988e6c16f39ca9354566fc53cf5e36dd891893f2a4db6a93e9dbc7c
key: a2ac1f30c16d14929a50a825fa6471f6
nonce: 78f0680c8a559a19182b9ca6
exporter_secret:
4e319255f9beef09159c1107cce952880a163b1e3187276ec2f8e33b1c0a4c12
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 78f0680c8a559a19182b9ca6
ciphertext: 61b5ac22ef8dca1b503fb54d276ee563ea514da40d91e0c10a164fee99cb
71672de98ecdbbd33cc3a3f42b6e9e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 78f0680c8a559a19182b9ca7
ciphertext: dd5309d12ff8811eb4a7c0a178e5838d48251382ad344bceab1cd58e43d9
d6c753b13af96fc38421ac783ea62d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 78f0680c8a559a19182b9ca4
ciphertext: ba8f6e8589e65d27dfaa10a4055d5794ff58bbb95ae7c43bb24ca006280b
40ccbbb09657a501137194906cc5a2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 78f0680c8a559a19182b9ca2
ciphertext: a582bb6eb2febcc90a6d331bd6c3b027cdf83aee2b7961bb0a9b38f637ab
b221e3cc4d240e16a0d6c0b84d89c3

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: f153e4126dbe9dffe130e979bdada4813232d73270a88219081204944e2a7e29
seedR: e823373647949d2b4492fa1d55eea30ca036a4cadf66d0af1b688fda01bd3f3e
seedS: 0a646975accc0fc1af028b485f05f96c4895b56b5bae1689d6720eeddc2dacc9
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: f3e87b72a223c8e3a1448ece4cc1e08c62bc7b160cfc27a84871b6bb8a48f04e
zz: 21affd3955783273df66084102dce4e0e8b585312b4d83ca7b6bc83417c07b22
key_schedule_context: 03f979af8f01981d30dc4dd8856fdb2f2cdc71ca4c38a64d1c
e95bb190bd8265ed44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 2cc9388ea324e42bb4ff7f4ab39fe31cf22a53800ab3dd9bc92d9a44c6008d19
key: 20474a19dc6bd0b844da1f6b9e8e94a2
nonce: 06be81dec73cbedfad54dea4
exporter_secret:
49d1ff4b078901c8c1e89aa723fc4b0cb58b45797f0247d0bfbde9c8a33fd264
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 06be81dec73cbedfad54dea4
ciphertext: 9036d7895a5c10f3765a93057d1e1864337823b4624941a5d6abe498791b
fa991bbb0e50f6a5a52d9b5f43232c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 06be81dec73cbedfad54dea5
ciphertext: da60ce1a8b45af49a81a8ace8d9ffa7210abf5803c54008a8c300b678111
5d3030477eeb7ce50cac3c2d2c45d5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 06be81dec73cbedfad54dea6
ciphertext: b54d672a0358e698084de8c2b18e53bffe436e41e89b5301c6f8ab732951
634ecb0ea4374adcb3276973a35423

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 06be81dec73cbedfad54dea0
ciphertext: 20f86fa9714e2765ac185f5c3c3f6350910dae7c9a3418e00bebcd9de770
d249c6a34b396679d6c7d0f93b7549

~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 5682fd4c2b0867a7fd205295f51485bacb64ec9faf2aa950901d87104776e059
seedR: 320db0622c6489f753977e0dccee6beb8e962637321dc561e7cd02526542a318
enc: 4ea82df931a4efdb9a5844c1384be1201473eb10e3d1fe860b4f152a5b25b011
zz: 74bf8408cf07c6edf3c9703947a294cd9fe19c036399e16804259c0cc02641b3
key_schedule_context: 0090e946219373c5e11230bf81daaeb4d30619c01503282248
fa28197db01278986da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 5ab5e78db54d919c34b6501dfc6279b442ed0044127e25ab9592002c1401df06
key: b18b4ad2bfd95d6500e9759678b653257e4cc05f483beec1cacbdc6706ac6650
nonce: ea151540c2a414abb92f9a89
exporter_secret:
85656e493b8d628154d3fd1a093ecd3ce6f6ad9c54d65889b241c0ea355b84b4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ea151540c2a414abb92f9a89
ciphertext: 151b2c36f4a34261f48168aab10cfac216dbd65e7e2b14e675bf607b7fc2
5e624ca035495a535564358b1ac839

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ea151540c2a414abb92f9a88
ciphertext: f0426fb77990c3094e8db6885d535ec3d150ebbad73d854134946d78bd19
8c9d108b36ecb108b4852140b614ca

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ea151540c2a414abb92f9a8b
ciphertext: ceb332cdadda58013ffa437936779c4fd0befbab6be50a3f13a0d5a58214
c8d395a51959c07a38c7160811b63a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ea151540c2a414abb92f9a8d
ciphertext: 4593772815fdd7b27c4660f72911ff7a7912de58778612c171f8f7134ddf
e68aa51d1fdb7b8ba62877bdc3ff20

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: c965c85a46eec5dd120b29ed3096198bafb75fad11b238968c6bcf8b04540f25
seedR: fac77f2e3f70194e1ed53a7eb1b992a750fb3d25d27bea42d596c1604f3e3d16
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: db00af4bd4cf85899f579b007ee04c2ce97cf822ddc28230d3e7ed9a685c9c1f
zz: d71c8d6128b116538faff89627c6c14870b5ccaf5185e6caf3c8258f6bb7aef2
key_schedule_context: 01277cbb8d87a2f79b27fb6330a4668f0ebe3c13a77ec5f70a
0f8211737d7494456da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 46af715524abb54e470a895938188dea0a62e508d95069515e5d193cc5898e97
key: f1f59b4405ea891ae7b971f7df97463884f9a8d2f493f9c34c39254efeca1bce
nonce: eed0ca12b16a4fdf39affdcf
exporter_secret:
85dc57a315cbf293b5d51a2631e2ab572872481843228bac4bd241a48bde1cf4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: eed0ca12b16a4fdf39affdcf
ciphertext: 43c7ea08087e0180e02c418102cd0c717be791b705cbadd2300a6a38b3fd
a90b71fb5ec6ce724f69f26af92e62

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: eed0ca12b16a4fdf39affdce
ciphertext: bc15d07eabb9ec40bf03c5a80e5dcdf5b8b30b33d1bf3859f75789c72b4c
99ab30059d96241bddb1ad4a737c16

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: eed0ca12b16a4fdf39affdcd
ciphertext: 4eb32440f88b30c88971b484b9b2ddcf1239e7fa3ae60b1398693c72183b
dd12d08deb1f0fcd9793ddda81785c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: eed0ca12b16a4fdf39affdcb
ciphertext: 8745b3220d2898b4f9f4221fba58b958a75456271f335e25ce59ee87df2e
f461a9131fc85818cf068a77621779

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 2e4043f500e44c8ad71de839b851576dd9be30f332fb34ea09e5444b8e616fe6
seedR: 6e039c779ff2432138457d6a0bfb10adefaedcf0556c095287fa15524d7836ae
seedS: d380f075004150f3850e86aaedf90ffc4857f21e252a74e2041cd6b5e2f591c7
enc: 6f519533c6b062b05f36f61d1111457a8bffa83c3cb0965515f7d50b0661b257
zz: 21d6fa7c23619432ebf3bd4c9b53102df01b9a8981cc1e38c32e39dfa9be0a22
key_schedule_context: 0290e946219373c5e11230bf81daaeb4d30619c01503282248
fa28197db01278986da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 56dea5dfba6bb982c49d5d3cbcdf8366b9fb63a1d4f2b273813de3c355beef0d
key: 14d16caeb6778ea02a13b5381d23a3b3b4ed6da914bb6dd59690e80bb70836d9
nonce: 497696816b425ee487a2cff3
exporter_secret:
576edcdfc9d1042c4eaf07d2f3faf560e12eaeca31e3bb7b75620ff86fc6b095
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 497696816b425ee487a2cff3
ciphertext: afd5dee6e32b3151d953bc66b8014c4e5dadce7d03c3c3a5a0301b5feb26
34b7634f3bad2ad17320fcaf40c121

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 497696816b425ee487a2cff2
ciphertext: 39c1ac8639f7d42ff9794dcc24422caef304fab7450ff961f270da4e7ad8
5fa579187ca1b7536b152683fec3b5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 497696816b425ee487a2cff1
ciphertext: 5ce32d9205fabb2269c07f84af46ed402dcac5c10d328e03d6eb4d669926
91b36137bd7df1c33f1f51fa9ba1dc

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 497696816b425ee487a2cff7
ciphertext: 918ca10fed979116cc948cb3150979c6ce4c905a9d1ee9452b21ab9bcea6
9be19a2e2de234a9e5db80994bf195

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 5bd83220e2d3460993bd567c6eae2bfbbf290600bb0bc55de51ed693eac3a993
seedR: 7cdde865993ae57616121fbf4ebae8cec0922ba138eeb482cfdaf3d21e2bc681
seedS: c37bd26cb7d51029f571874cc8e94b8055e065cac0065e33b5841e3d8c013076
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: adeba4df5c320db81c1cc62d3a22d333282b5f11581d45bc37a6f01276078b2d
zz: cc41ae9badaad6e6a10069bd48806ba4eb6647c6fbefe343a961ebcd616a9917
key_schedule_context: 03277cbb8d87a2f79b27fb6330a4668f0ebe3c13a77ec5f70a
0f8211737d7494456da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 9c6060a8f7f962d3e5637ba8065663fad4de4f8c0a894a7dfa135d04191333cb
key: b5b946ef5792a3e9450202039cb136356d5fc1a9c34ca6c3865a54f36ca4cfae
nonce: 7b992b49e60e8b5a8960228e
exporter_secret:
28745bfbc3f2b93794cd528221ae445643de62d592a468dfcc19a772003c0b2b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7b992b49e60e8b5a8960228e
ciphertext: 0279165bce350d8ae6a8dc481c5452f7e7b20e90e5bd153b4118732dc7ae
55633275bee4399ec874e65ee335c7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7b992b49e60e8b5a8960228f
ciphertext: aa0493edb0d08734a1e866d937130900b505f93c5a0e3f03a17c912c88fe
b68879ec84838e5660c370f6073e45

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7b992b49e60e8b5a8960228c
ciphertext: ab982d976fb64a30d06a73d11ec634aae98a289955617b75bb0b3fbfe619
f129b4f9b5d83ef90a7855f8cc0ff0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7b992b49e60e8b5a8960228a
ciphertext: b290ca66a67d573f6f51db146e0e15a674a8532db3d96dad9c609db80f14
92f48445128058ab5950d6fbfc015e

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: b474907ad8064c4261b14ae61e7a322772227e4ff0655a2b3b2f1cde95bce33e
seedR: 56413134ef76cf67de227a3d59609452456e1752156b2e0c1a841bbb5ef5eb14
enc: 04d1972f22b9dd58bfdbc143f20caf0e83b2578a6bce581eeb81850ae7ffebee28c
f09d0bcd4e4e6889484c6f16d9b2be046558759b690f81c8e27579b153dc5ec
zz: 5f748c74bec5344dcf64acb0bd91422dc9ffc429e9ea649234d8b11881c983c9
key_schedule_context: 00e64a9ff5bc7127dfc36e8a02b15ec56345b06ad97664d3e5
c731bf0a10c74593a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 5516eaea348faaa44dbab8eb6cf4da51abd6078e42474c95c4051a005d9b6d58
key: 7fdc61cf77afe80bd9dfa2b6eb3e0f07
nonce: db7d6b5d97b9aff56a7e31dd
exporter_secret:
ab5954f45ee8d86f6cd3e1ba0ce6bdfbbab7ea284c625649579132993b4673e1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: db7d6b5d97b9aff56a7e31dd
ciphertext: 8b7d3a1dda6cbbcaf41f9e0ee0be037dcf8e0aa683911ee73f1cad879b8d
4fecafa115b369bdb00feb9bf400ed

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: db7d6b5d97b9aff56a7e31dc
ciphertext: 3845091970c81239743beb4d670b6338d505e2fd5fcdc30c0a779d61a67b
7f78fd9fab399d89fb850affa62877

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: db7d6b5d97b9aff56a7e31df
ciphertext: 8ffdf6fd7e9bac00b9679a4bfdc72364e0ce279786d8ebac6a6cda815f9f
ed36a9c5158a80d76725b4ffee64c6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: db7d6b5d97b9aff56a7e31d9
ciphertext: 5a1b70cf14b78d97a46bdd0e4cc3e9eadce1f225b602a82f39e45666216e
0eed2e72702c323baa20b0140f54a0

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: c0f3f2f2a1de2e354840aeffc24f398bb82c83bc34244ed60be79b61c5153b06
seedR: b52fdf93e20c977fc0c95945c6d7a8ecbadf55eeddc5b993333a4c3c562e1e8b
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04d1b10902566c9eede93d8144c0c948a96aa95b96c53871fc3b8197c0a37615225
d3acf52a0013e02b45a9862f8e865170a683cd487508f7acd3c303ea477583b
zz: c356ed7d9cb721604cfb61448ba41354c50919d0c16bcf630f7db812066df796
key_schedule_context: 01b790c8a7d9e02f8dd8b03f5ec747215050e50fbcbc0e1949
5b411da2d1b46501a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 12c65084512de8361df900c10658072ffc0bc2d52b61f39203b8915991bf7bd5
key: 82499b8847105b8e8274df054b88deba
nonce: 92f7704f1449b1f1abe83fc5
exporter_secret:
a7620c26170223d8d548fe4482679210d0cb38e6578f6d5130ae4b031f30aad6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 92f7704f1449b1f1abe83fc5
ciphertext: a382fc5fc54b690a87325f9d3b0a85d987007e2ead6e663ed97f80911174
25a4746e8807da17158ba9730bb2d4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 92f7704f1449b1f1abe83fc4
ciphertext: 43c78f89a7ac12c1acf4fa87b1b856d23132de7d5c43a75ec31c53cf57f2
64b2e338697f2d8aaefd9855123158

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 92f7704f1449b1f1abe83fc7
ciphertext: 16b3ac762968879f60a586fa0cfbad76423b45113fb3c92839d91991ab6f
434ec70c1f620b3f2943315be00901

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 92f7704f1449b1f1abe83fc1
ciphertext: 0a8ed897acbe1732536f655533887899a48e465131ebce7839d944a379a5
c087473b9e369d6234e98b898e7f54

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 20c77bee7b0dc0577d8ffcd0b4c6731543e569602b3233b59bccf8b0732e0025
seedR: 2212c865d3800d54c214ec7521ebaadbb04c63bef5fefcaf4cbb089191a49f38
seedS: 6183ffac7816eb0629bed018cca925378a197dcc79b8c1f9155eb9ce0b921e1f
enc: 04fcd3356f870493e8e3023da14b24c8e7fce45cfb62657f3b6a57d2bbcdee1e410
e423b98eb6e1ec907393594aba2b4ae519c8e6fe42104bb70d423804faa0a2d
zz: b062375b247720f663cb7ba9da7368a0eb2a8c3013752c3cfef22164e8200ff5
key_schedule_context: 02e64a9ff5bc7127dfc36e8a02b15ec56345b06ad97664d3e5
c731bf0a10c74593a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 7240dae294798a5f63436a122d1f2e775a0a946f0798d6b23a134369ca413d7d
key: b61413cfc7ca6f85f058340f4169370c
nonce: 1ee2921493ca0ec1162eedf6
exporter_secret:
ca778763dba2b7809a8f916ce0e732e195c6686fad8687d311bfc1021a0aaf6c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1ee2921493ca0ec1162eedf6
ciphertext: 88b49a3e27d9688682e5008629cdfdc0254004d2823d58ca6c9eb208918c
b28dca251b8244cb3e33d33f73de2a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1ee2921493ca0ec1162eedf7
ciphertext: 586520f413771a3e331c7aa7883551a31458a0e741bae737706a5409ce12
42687eb218beb79742988b65191d4c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1ee2921493ca0ec1162eedf4
ciphertext: 961576c0ac23e933a33d4d88491f5a530874cf634434e1de367eae3388bf
9f9a9b62c310f557c0926dad23bc27

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1ee2921493ca0ec1162eedf2
ciphertext: 7963895d55effa634bc373b919ffa598382a6bc78a4f0970f915a1364409
777df9c2785a3df9c4d975e4424eb6

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: ae494ec993065f1c61adb0c134314529a49df4b17d70bc8e0736e94a6d66b9a7
seedR: 8e9e6737dbad4c4f8507679e3af9aecf48e271797b9c0984f303c4772e1659d0
seedS: 4b428c475c6431b736008af79c899106d9de7a789c7641fc1be93fa1a33ad15b
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04a3f8d3ed6b50706ddaaaa26630975343ada04d7d7294b9df10ecdc38976b48446
57e988f9443b306f6b1edeaa06ca4871ff052fb8f1d935c4cabceeadbe8027a
zz: 8d1a04ae436c0f9ef116550d24a1608c65d49f38551cbbae19d41ecaa8e61494
key_schedule_context: 03b790c8a7d9e02f8dd8b03f5ec747215050e50fbcbc0e1949
5b411da2d1b46501a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 87fd9dde31df15d75b86c7951441fdb6a0cb951522b3fb1ac0b9aef767215d73
key: e04793fe31d68fe8174bf9b760094250
nonce: 5b014071b36f0d29a3016304
exporter_secret:
92272020587f528496eb0a12052cfb86f29ba02e19f72fe85b2af97adf1b03e0
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5b014071b36f0d29a3016304
ciphertext: f2c878817c668d0ad6f3ae37e07a185cccc644a8cfbc7dfe3c214a12651c
b65e6464ead67aa0d27736364744d9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5b014071b36f0d29a3016305
ciphertext: 5ee11a99b68af253d3bcad7037091e93e9a49921ac98900029cfb7d87157
8d3e591c2284f5d9cb7795087460df

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5b014071b36f0d29a3016306
ciphertext: 1253936a922b4083ee4b1ed84864d5abc839c480913b5ff3a4f4b3c7cf12
5a590396ade7c9c36f373720f98835

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5b014071b36f0d29a3016300
ciphertext: 35aa1f74b2dad269a601591d21d7a702e8800ae92ddc455d8b5efdc8b49c
24739a111a8aaa50987840e8e8593d

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 368185a2b5200b45ec8a42736fde4dd5836a4e87a6c3a226ea8bf2d49836f794
seedR: 32cc1745712b850dbc9ccaf676a84e6c9aa109234e2d96361fb588634a21de24
enc: 046758818d026e9aff8f59b0b3a9fc3fb33b89daa81d21b1be871828da2f3243b8f
c6156a50fab544328cb982f61f8f07b1e78544b00842e882270dd0302042fc5
zz: 125ce83d27d476b5fd69728962a9a35bd99db73a2f2e99831756a9903a591f4b
key_schedule_context: 009ab0871b0475fd24dfa8c9e401606a4d02d620a14165c3bc
a7d55323f7846d8ad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 360ad964fbaf636325376885da089b24b88e3b82604139c6d3658dd8c9bbb78e
key: f904f7bfaec576efd0302225a3f9a44fa957ff5a0cce9e403e30835f70f30f72
nonce: f931298447f56522f4a08213
exporter_secret:
ca8d9b7f2a309482c926f84f70f358b54dd2a1726a8bef73fc50ed5845c4492a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f931298447f56522f4a08213
ciphertext: a4ef99ca1f5e8c2e90c5dcae24acf43aedfa8cfefc149f03942af9dd4513
ecc6ed496b923628b8a579ad10947e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f931298447f56522f4a08212
ciphertext: 21ce75c0ca516522faf30956a253d0c2ab8eb0a380db99a4f9b02f72795a
9f45f2a38f2022031297870a9d1897

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f931298447f56522f4a08211
ciphertext: 660069e41ba368d0c906cd1ecb1304e49ab7c8a31686edcb7d4419377e8b
4c553e6f99fea35815040e7fef2cf7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f931298447f56522f4a08217
ciphertext: 0a9b355702a3c5041af7db23711dcbff12dd66a19d4dda2a3fea8c0cc3d4
d9c4ddb2f2fa27187d813bc201c8e9

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 1fb6e53004a2c54c337cdc7836d72ac13e97988570779e6c6985d229e749e5da
seedR: e70f70e26463fd907bae3549282755cab491ae46ea692af7c33b851ef96db87a
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 046b61691ff7e98c47a05fd2f82412f6116207fb45c8c6b37faf4f8cc2ae240c9d4
10761553074bf8ba591bfcb74681a3128d474c8c256e7b1dcb08e7e2d775c83
zz: 7ccf5f08dfdd63a5f62866351f66682de6e12fef72d907f6117210c938811251
key_schedule_context: 01a700552a480322a610b7d6f2578174fe84ca2418e75a3166
a4ef46409219745bd3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: f60299df2093a86a4b12694a75662ae9a3f2c5c6062f80bc4775a2528f5de28a
key: 9cc3a6dc671094bad423f7a1203b05012dbaf0fb0d2176f661942f23bd243e48
nonce: 3824a445727fb67ec29c579c
exporter_secret:
d5b515158f905db9f2614674aa6567e801bfdc6f5d39a94f6be116867b8ad325
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3824a445727fb67ec29c579c
ciphertext: 49b9e75288758412df7a35edd40fadfd52421d473dd4094bc0cc28e58599
6ccea2278dcdd91a371b49beb7caaf

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3824a445727fb67ec29c579d
ciphertext: 11e026e40040eaa1cac3cda5b9d372dea85e6a1c969109f8ed2360cc7469
1f20360c7d7534c280115e11e31f9b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3824a445727fb67ec29c579e
ciphertext: a790100f9630ef1d09b9c1c31e42a926ad2830c20e85c6b94c84cb2ad6fc
cd68451440ae3eec668cf6e2156123

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3824a445727fb67ec29c5798
ciphertext: 581abb2837366c6a2564733a9722dea291a071ed5ff74bd4327ae8f2a04c
72b0dd67b495799ab55087af49515e

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: fd581cadd8eaaa82ef86dd673ea452b71fe61b8354111cc938332893475df48f
seedR: ee1311bd6f9a0311df4043362c113c13f933e235684102cc7068f635cfd62019
seedS: 2b6847213881191c2ebcd5f4580d99dc8852ec0c02a5e70a7e9fe4bee9fcf8e2
enc: 0461acf56b014d5f62556ba1b3bb9ce82ee010c45447db80ea5d7a7a650840779bf
ee75ff446a9e0d6bb5bdc648eecea0601822d2053ac69316be908bb7d6b73b1
zz: 6162e3b3f361f682beb8fba91a7ac37650931f209b8b911d7ad3dd2d3b1835df
key_schedule_context: 029ab0871b0475fd24dfa8c9e401606a4d02d620a14165c3bc
a7d55323f7846d8ad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: e2fb7d17b45fac5524579dc5e1d239c728332ce64b1e8ecf1eb2d77210c82b03
key: 98c4f3b053f74b14d76d6c5449515083ee8a6de59585fd10211f2bbba00c5ba9
nonce: e3cd9d52aa433d434498272b
exporter_secret:
dbc7fec68c1e2b7eb30fbeacc99f53aba4e32cbff5baf059bc32341afc9bfac2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e3cd9d52aa433d434498272b
ciphertext: 93765f0feff3f1ea48cc16c7e8ac595db1b30f37778fd256e1b0ab1d2b0c
1046be1837992e89cc0209dd0bd2be

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e3cd9d52aa433d434498272a
ciphertext: 9b31884a39d2720d12a5a2955e905a0ac7a1de847c5688c6f7de4de881b6
de49ad69eee1717a1559e32d80d171

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e3cd9d52aa433d4344982729
ciphertext: 6ffdf05f734c7af0120a7c36a0f72f3db0f137d2cc10784aca2ba3ef1dc6
48351afcf4d90805902db77a3d3046

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e3cd9d52aa433d434498272f
ciphertext: a839d60a0360d97bea29bc31cbf834d9b8a4acfab0d76ac52e53608d26aa
6a9f6fafc24cb1fa6eedc7b3adc265

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 0d576bd80b888d08522b73d09d5f82fe192ca18f757491236265f81342a1c775
seedR: 2b169596d12b012c1bfd85b225c70a8a0feec2c84b68b20623c03de25a32ccea
seedS: 54d32270c3beb125635ef5d8e33835018d7a228a4565bdefd5dfab5130d78021
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 040ca1029586e25c0a517917d0ff5f8b09634b2c8631b802924981348d725ce36e2
c23683a720e55cc9d9a4cf8c8d7ba0a92134299f3af94e5729c2bceb44dc0bc
zz: 8a39c431b3923b508e4c2811f2a92bac656c9d78d9565a1165897a62ca084393
key_schedule_context: 03a700552a480322a610b7d6f2578174fe84ca2418e75a3166
a4ef46409219745bd3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 097ee59c355d88317956cb436edd60a62cee7a5ea94e6c12d559d78f1c0ad779
key: be8cd2a87fe192f18b2ed991b734d267d658c055398d750a0668aa7c216c69ee
nonce: f83422113691c1a88a73b02b
exporter_secret:
4f68060444dfb244bbb6ec2c1581f56c86f82b2efac17df04c11c5eeb2eb0b65
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f83422113691c1a88a73b02b
ciphertext: e4902db8a1c14c3638fba68cf82e648a1236a0577e11e0b5401ead7e0773
437cd826018ea94b697d186f268bc8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f83422113691c1a88a73b02a
ciphertext: 4d66770f2a02b5f8a6c11a6c1e6f998e77b7985a98bf2e12757d2f8eaeda
ec586e1490592ed8424f9347c8e56b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f83422113691c1a88a73b029
ciphertext: 1409b920b04b3a060a6682ca99c7a28e03ea6a697445a95f7e99958ca81c
ff4f537ee548329c79d35460c11963

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f83422113691c1a88a73b02f
ciphertext: 066a2c9fc7169215e310f21730f69b935bb32433f055486942f8c1009259
4fe6d15dbdc83ea1f8eda99459df9b

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 870585a689e05588e60cb0a7f7412081119b9ed26fb6e6bf4c13f8f17c2c35ab6
656f37e5ae90064651cdacbceb88f81db6403997fc816a4dd1ff3740c0b69e2744c
seedR: 78895d536e0c3d4284377c6bd98bf9ad7dffb563ebe6505ff67d3a783b1d8474c
286a7d0c8e22407b3f27b91d345654cdbece12ffe0f217b6e16b39c85a5041a3de0
enc: 04013ec7f0bea4d8f113f2b1987b871e59f2d34705bce29a1e485390bdeafe3e43a
5dbfc1940d3487d58625d595f9202bda22dfa53348a2c3c2f186e13bc59a87b4b72019b5
a89155d547da98e9b2df514da966c8050b293e37f5fb219b2da02babae2c602ed49885cb
f7ac752f17e01c918d34ccc703872df13e29036f76a6084572eeaa2
zz: 2d61f47a2645f95546b9a732a4dbf471affbefa0e5c774d493794e945d91e4bcf1d5
b91da1be58f84fd6c938d90568b7065f09f1985066d4c8508de39ca68066
key_schedule_context: 0080cc07c357b2a135c6be3f3e2c99451a40cb78e474aab368
da431375508c61973cd2bc12305873be389d8587221aeefe64bc42c8af42877db4aedadf
53ddee12d8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: d2753c3be8bf20ab2e675ce77c2842ae11471e1db6513bd81a0dc9a2c267674b
13fd78de31c1746fa953d852d4fa98c2a8b357e065ef42ca5af5cdfca495f3c6
key: de50102f3f6684e1e221d994357cb0e49fc6240b6b36c831cdd3df963befab6e
nonce: 28981c00a6a3323e7b64afc9
exporter_secret: 1b6d9dee6e757332c0bbe65e625938c5535451a97f190a2208dab8f
74802542b544e033fa2a28cbf8bcbf49ff4e3140196a98da1e3f6ef42ef08047d6ccc1e8
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 28981c00a6a3323e7b64afc9
ciphertext: 7e76ebdecca47c67c85d51709defd2779a82351b15a435b3511926465b5d
1de5a478a09de5f43dd09395376419

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 28981c00a6a3323e7b64afc8
ciphertext: bebea510c57a0cc54ba73bc4b30c4504091f8d8565a444e3f1d386fd1e1e
27b8543be40880a0da2e4aa2628e02

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 28981c00a6a3323e7b64afcb
ciphertext: a09a3decc57324dfa2415e573dcd1e66db2e5ea0afdc960c52c03fff742e
b6478398dc22778857a9325b779159

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 28981c00a6a3323e7b64afcd
ciphertext: cda3cbd3a8946ec8081f9a275b4efb2826f9c9ee0e0d2213f30695933fe9
62116d5b2dcd308f3d5eae730cf5e1

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 1e12ca25dfba12816624d497eba5aa0f598c9ff793fa092642a856a6481f58dfb
eafe2ad5ef817d5bc8495d9514f12f86796857df5e33f6c22290b49df6e00ae9bd5
seedR: fc63a9363653d526d0372274de10bc3df7ec8b60a9adaa55c86db5155c882a7c3
7da1dcb3177e881277fe7ed7a4b324dfc63e7773b9adf2649d47085f2ca0f2493f4
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04002c03de1ea9bd87fc95df0574bb5ad77277d73b4a422f39065258dbdba410800
e6bc10df05a9076f1ffbd17e0921cab784f1cb651f9cef709d83cbaa768b8e6387401919
91ebf6195469eb92ee6aa8e6a3ce3bbe18dbcc06c5b638e18fec7c9a124f47f9f47050dc
857ed23a2affb32f3d8e9b2fefc18c140cee39fafc41f6e88c370fb
zz: a3b65884e2c2ad6af08fdddd01780d696b3427f4fe1756a17e8740166af1408fdcde
aab9617ac1014459677b89fdc235e5ed7c3936c04b1b1845e98693195870
key_schedule_context: 018e78a6b458ea0cb85f3b7aab800625a43538aacf85aa98bc
382be6cb13d3c7659733aeba29a0e39336209d1d641c057888996d22464228de4b17af1f
86567b0ed8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: c2560749f616cf2f0f619c2592a777b4247bf29c1d061d80240a02d628eb9586
742b9d2553f347b38e4dfa2d4c72d24fb4cd2a559d37bcddd29bb14eb6cef323
key: b6e855592d3232eb398efee0827747d55301e9cec4f058b41df16a112bf2d723
nonce: 46ce7f5a5d578933e086d593
exporter_secret: 607af72c85c18db1dadf7e60f92c8c7fd0e93d5bd54447a75277129
660635b0d58b5414a4e0baf48f17faeba033f0a50e8b52a2d717879b876c3c53aadc9a83
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 46ce7f5a5d578933e086d593
ciphertext: 16561de6ac6eb9e7632b8ee501fe915c35daea75a7eb8c5ecfa469560c86
33c6973323b06914fa8d0a41796298

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 46ce7f5a5d578933e086d592
ciphertext: ab08fef03db484342267f25d35f220b16894ace6f005f98bfaa5c8429594
fe52452b27f1126d69e9f5c7c3e776

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 46ce7f5a5d578933e086d591
ciphertext: eb1fdbbcaa857f0843107ec6ad6b6365c3ce2acdfd214cd8d77ebc309862
d209b5ef72dd9d3a143f59028a7a1a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 46ce7f5a5d578933e086d597
ciphertext: 9cf9ff3060c9f97fb231d62efe2494d7451d8b1a602d78b35f72fb6d8f95
f56c848715241432d8fb76d0b313a5

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 939b485d91a06d9fcb9d5ab9981fd5f0f21621b39d23f0e7ed893d5b069161b34
242c74cf9d6dbb7696a81ea8e48fc86ebbfae354d08807a07ef771d9623b5ee0737
seedR: 5a11b68dfafa9fbb236f69b3aa27e97906bfd7d31bab592e9779fd96010fc2e9a
f5ae3ba96958063720dd3ff5b28a7e8a5041023104a01019e4802d74f49fa7e6f58
seedS: e8e18a134c4934ec51f5c28d6da5e78972f9f658175bfcaaa3c2540f87a712f4c
ef83ce4ca445671ecc8d3437683754fb0151a90b83c2c39a411eeebf014ea89548f
enc: 04011ddc56b143625bef2d9c8b1a3a1bd1f3b9800cbc4346bb9275c66b4c5dca228
9ebf5fb7e6ea57f0a610b2e4fb25418049d46574ed4f659a49490f01c57bc912cdf00d7f
b57b4cae8073aa04534f56534f4ebbfa53675d66364f7372bef2b05d206a120493cfaebd
251b1751b6eab90ea5fc1e5653778d63e1f6af8bb0f6a60c40ead2b
zz: 5b986a7fab5ffac16dc8d4ef354468c94d1590dabda5bcfd0adcbc8e8e0a6d5548bb
8575294c6e05f7a07fda140e9882b518ea4b646009cb56003356cefd1dc1
key_schedule_context: 0280cc07c357b2a135c6be3f3e2c99451a40cb78e474aab368
da431375508c61973cd2bc12305873be389d8587221aeefe64bc42c8af42877db4aedadf
53ddee12d8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: ba50929f6db4f0ebe25e27dcb1773f6422288bffd27b57599f384fefafaa8cc1
c68e299c6264ad787a36ba22e7844b0afb4afcae6cf1c10dcd43f28584300007
key: 45975dbfe04fc6d0d4d5f94c4c4798bff05c4113931fe94b621dc7fe23dd5765
nonce: 3030d5e926b32a23d3db3f1f
exporter_secret: 12dd79bba740a46bd8d41824858eed46eff408c0744a98e8058cc2d
862a8921f47ab1e8279a8b59f7ce40a003f3f82714235b7aabbe3a54e80ef4bc893e637f
6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3030d5e926b32a23d3db3f1f
ciphertext: 1d9266ce7e481d7e0e5da30cd51dad7ea60cc5895d5cbbded1d6bde0b227
28db06cb12c726676ff4dae560da20

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3030d5e926b32a23d3db3f1e
ciphertext: 1078182806441a2071163c5a71de543f11deb1dc92bdf596efba60d4e1d5
00e7529c644cb49c0fc6158ab0268b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3030d5e926b32a23d3db3f1d
ciphertext: c0be6332c417c4c51849d58a191b9ebfa8d126b9db6ae8a6412d8b84d5f3
918124ff652ee120eb3e2b5807005f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3030d5e926b32a23d3db3f1b
ciphertext: 4361b01dee5f3c9c59019a362fc85a97685631ceaf98f5084e8443483aa4
d5eb1bff92fb2200dce41302498e42

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 1462b8c16fa9f1f7de887bfffbf24640bfa1675883d2216914726afead8d297a6
8fc6b4ba40dad8c7fec2a7d691a44abbb50af68b342da31348da94bbbcc6297299c
seedR: b0ab9b28f9c75df2a27a9407c58a3d9941f8beaecfb243806042199ad16ae4aed
eca4c6dcc85ae6e0aec70cb1c72fe0ab622a2e4f227d8c1da4c6586ca83a985cc77
seedS: df8793c3e144312bdfddf748148b8f0260cdfb44ee95a09e653fb1a536c4db1b1
ecdac4a1208862b2fcdb25ec2144a9bb03ce59a6badb97a9c368bb7bd37bcd00202
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0400dc45b2730c5d4c7a5c112634a9465b6d03c175c5fe08b273bfee30d69264328
edb2428519e554ffd3f07a17680543700e6615d6c96688ec80296dc01e2282ba471010c0
aaf52827a9f0c10ccab7c5ef7328252c3301042037b9e4822e77a1648aa3fe2e57bd3e6a
6b0c0578ac1f984d4160ba5b8625b9373d36e3e5d8a88619fff26aa
zz: eefdc47f88cf562be429772c6a5b286ebe9360f9e66946ab7d0ea6537f61533b52ca
e5ae976f2fc4b257d4a5569f0513b27e2614aa4b0bd5fad8d88ca53e1a30
key_schedule_context: 038e78a6b458ea0cb85f3b7aab800625a43538aacf85aa98bc
382be6cb13d3c7659733aeba29a0e39336209d1d641c057888996d22464228de4b17af1f
86567b0ed8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: 95a66b1609e4506e1624680b0903e21d91121fa1de57c633f0a76fdb56ca8aa4
65481672b059d60c57fbe2bc0621b5f6500b82bf12f08a686d96a78db4de2108
key: 3f197599f89a77bb363f151da98a02e60f430f0fb8ea15b513528e92de7c7cba
nonce: 63b2a2d4aa1606ba52b49914
exporter_secret: d7e31604ee88bf78acfbc6e3a28c2a4d38efcbd54a506b34696463f
eb1f8cc1b9c0e044091731f27e6466245a8a6d49695014bd8288a93f01e2e2c87eb3a07b
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 63b2a2d4aa1606ba52b49914
ciphertext: 4fbf78dbc158be6c0a02604907e4bee97e4fa411ccb08f5097300680f035
9d3ee4fac45346833bcfdd53e83585

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 63b2a2d4aa1606ba52b49915
ciphertext: 7c20093300d7da89a37aa4673dff2a0890a42fedbc495739b919df6af430
61784671cbc3a033ddd6ecdecb5768

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 63b2a2d4aa1606ba52b49916
ciphertext: 2b330f0381c4ec7c60dd4656c5fa38c2874e2e32ea66f31f9dd9aa683488
98f934db054cac40b33ca56fbfc65d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 63b2a2d4aa1606ba52b49910
ciphertext: 813c66bcf6feb63f75f8dce51bca66ff1eade817ae8a410fdb0aaa4832a9
339d53bc423f677e403e39855f5de9

~~~

