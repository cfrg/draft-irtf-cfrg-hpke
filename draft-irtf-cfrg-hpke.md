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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/fef8e58abd54dc3247cdce3cdba7c00e0c879c68/test-vectors.json
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
  labeled_ikm = concat("RFCXXXX ", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "RFCXXXX ", suite_id, label, info)
  return Expand(prk, labeled_info, L)
~~~

\[\[RFC editor: please change "RFCXXXX" to the correct number before publication.]]

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
of "RFCXXXX " in bytes and equals 8, `size_suite_id` is the size of the
`suite_id` and equals 9, and `size_input_label` is the size
of the label used as parameter to `LabeledExtract()` or `LabeledExpand()`.

\[\[RFC editor: please change "RFCXXXX" to the correct number before publication.]]

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
an identifier different from "RFCXXXX ". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info`, `psk_id`, and `psk`.

The string literal "RFCXXXX " used in `LabeledExtract()` and `LabeledExpand()`
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
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: a4386430cc425a34cb4dc59b6770504b87dfb40ea49314b2e2896d2abb4c6168
seedR: 887d7568a924f21f2736760a98ffdee7961bae159e5718c277cc86c34d9e6a1a
enc: 7d832f404f70071d69f285292f0758291f966274fdc5fa494bf6f1bbf81c2252
zz: a7815531e7ceb236ddf324d38be707652f807da5fc2a92c4ef930cf1b4ed2b83
keyScheduleContext: 005f59a87af52c687cb9e55e42cd7be07d4f1714b7c32c158603
7310f1042ce238e2315be921bff8bea06dd5e9a1813a3f909b9eb7a8dbd90ac60b906e50
ab910d
secret: 92618dbeba8b439353c831055e702a38d04bc194ec9f3980f349eeda6fe4a833
key: 7aa0d855767daea21e59a0bd8cd5559a
nonce: 3fe5faf065fd9c005755dd66
exporterSecret:
bc98ab04d503d3876233fdfdc2c78e253997f5861d4c72c70682e8fe965b795c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3fe5faf065fd9c005755dd66
ciphertext: 437ee37ee8210fcda87a7aae7c5e97b0caf37b93e70b916444cd9762fa3a
a2fc877bae2fe16dee3924968063bf

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3fe5faf065fd9c005755dd67
ciphertext: 448fdab5b1331bc2daf1c3e4de42da186c1180235cccf69af0062cb22d64
6e48cdcd8babe828c3367ba1056c2c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3fe5faf065fd9c005755dd64
ciphertext: 78af7509a1b84eae6f59b1bdccef888421b020a97f1a6be270363e5c4500
5389418e73235a942f9fd46b37a352

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3fe5faf065fd9c005755dd62
ciphertext: d4939ff18065a54b1e988c72649aa81b1bbdcf9496d150efbe2c03c084f6
477653bc03fd58a58a03d4ab78e47b

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 76c93930b53d48e43a1388d499c537b4d18f282223fc0377a38b3ec678ac17a1
seedR: aecde81a39413cb368a34fe373ae4d0b04627d8c4c9d314be383a613190489cf
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 0c0e9fb920a836c5ef42fd393589ac9d01af39f52c08caa7d80df9fec966d74b
zz: 5d9866637d1d10db5d9e80e672d5a249f083eba7c02d928ef81446158dfd151f
keyScheduleContext: 01dd2330a5ef651db37cebe3393a6bf27b38c3f8c4e954a5fe3c
61df61ca3d8cb5e2315be921bff8bea06dd5e9a1813a3f909b9eb7a8dbd90ac60b906e50
ab910d
secret: 39359ef40e95feeb2cc8274af171cc9144733a0d06a007bb570a7718a0e87abb
key: 9fcd938926bff5649971a302cb6ad4e9
nonce: 52aaae05295ab893fc603a3d
exporterSecret:
097204ac8b3f5bc894e6c2daeea4555acae24c069e9c9b3f60e57eba46322efd
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 52aaae05295ab893fc603a3d
ciphertext: ea822a474afa4c7f3068e6094b6921972040091bc8f623aaab7a7c4f3466
07b7a8736d78fc24a0ad9d6948997a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 52aaae05295ab893fc603a3c
ciphertext: bbe0e814ee486d1089d87d3887d83445094dd527deebb2de29e4cc98adc0
ec3ff2eb89b8a876c9c60cadc45d65

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 52aaae05295ab893fc603a3f
ciphertext: 9aff8102a2e733203edc9515c23140a3ab4b441efc31fdf589b6d30035a4
5e442a7a8001f286f2df183dad6d8b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 52aaae05295ab893fc603a39
ciphertext: d713dd26d7cf97cbf71066fdd3f050f0b0b01f966ad776682903fe438adf
626fa754459e124e8a296e1d94170b

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9f06a1c6641f4636066457ed4a502a8e23573f579ff2982eef6045b4d863d2ce
seedR: 87a91eb9ef6e96e901df4103d1671314aec5ee6474d667c0c2b4168c0e22b1c5
seedS: eac00dbd269e725e8859e3862be47bfd17cf2d47e5be094ae77ff0ed836e7e95
enc: 3f593e5fd05782bd7bda37171ae5d794ec6be72d60495a673a0764afdb7f9a53
zz: 857c81b1681ede76b437a6075d6f93f348d5ae9b51da78e95d200b0196fc1e37
keyScheduleContext: 025f59a87af52c687cb9e55e42cd7be07d4f1714b7c32c158603
7310f1042ce238e2315be921bff8bea06dd5e9a1813a3f909b9eb7a8dbd90ac60b906e50
ab910d
secret: 15944a2b4517e879342fe24e6ed0340b32d4a44a2b2c6c2e83bb626e5e14cd12
key: 4f6826cc55ce4d0d344bfbe590855daa
nonce: 2465c7d4270d235531c3d695
exporterSecret:
f862a23f69dc83f0de76fe2546764c9c1d23dddedf8c7a0cc50b3e0872fb138d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2465c7d4270d235531c3d695
ciphertext: c37551008a6b7848ebc9d062c461f02d91323f4e5bde9720d4a53613bd63
39112b287ff7b66c79cff05890eff5

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2465c7d4270d235531c3d694
ciphertext: 4a5c4a6d0d20f6e1672a32fc757946a80bfedf17bfc6f761a6cb42b3bc92
75800b6af087efc903b00a96ce276d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2465c7d4270d235531c3d697
ciphertext: e7c100bbfeb8c7264587fb08efd9da552903175f752f70ee0feddfd5ca37
32ceee38f9e2df8a55d91d28428c7f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2465c7d4270d235531c3d691
ciphertext: febc849423b1fa5d750f1f9c599c2cc7d45ddd5d3667132abaf7de0f3fec
985599b7f977edb91ab93d33af657d

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 3f56378b5ec0239842e4be3aeac8ab5e0adc8190f8cc356fddb722df3911d778
seedR: faf28a99df2695912139d1b61b8e7a94a79f88e12d8a577fff9e3b49ff5e6ec7
seedS: a2e1018c6a854ade9cb5d69bc582b107f1c20e3763bfff7b7d23fb9b38fbfbcf
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: a45fd7250d40aa64a17f8e14e4987513086c01e7a753a43bcd03176a0f8c4606
zz: db00fa0e38cca7e958979d8ae5f8e55f5a13bfbf1be1aadf8de1ddd13dbb7ed2
keyScheduleContext: 03dd2330a5ef651db37cebe3393a6bf27b38c3f8c4e954a5fe3c
61df61ca3d8cb5e2315be921bff8bea06dd5e9a1813a3f909b9eb7a8dbd90ac60b906e50
ab910d
secret: 58e0302d66abf9bb268435cfe1e0802b4c3ac1f1e16f03f9795db038c88a2887
key: 4c79170f71e74212557131685a7354fc
nonce: c7f42ab714a4606e414c05b6
exporterSecret:
d65c46f0189bfc224e894b11f128fd528941178f028360f4bc2379862ad60e40
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c7f42ab714a4606e414c05b6
ciphertext: 56c24debbd281afa727712725c72a40834fff4920c8d9aeef3b08c684c29
97a2d0d2b0fa2768c4823c7e5212f3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c7f42ab714a4606e414c05b7
ciphertext: ffde5f5cfbcaac29450846b02499831f6db54775fa7c68e3e6a6f28cea6a
70bd57ce03c57cb339bfca09c048fc

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c7f42ab714a4606e414c05b4
ciphertext: b8e91378fefa33ef428173db4d64cb3e15c1cbce7e9d1f129884af766798
bed723bec7ef871696dd4ed72e9cb4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c7f42ab714a4606e414c05b2
ciphertext: ebbc30676d69daa70a91c654b9cb1ab8ae8af629bd6c909a053f3cea2421
07fa1170916a4daa273038b52d1b8e

~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 8b76b8dd43faf7faecf684ed9cc5b4cb937604d34b4f8efb830063ca047c763d
seedR: 2f74ee420165e497b22d2d5148eb66dc06e167e6b6a25297eb4d96747b86cdf4
enc: de17360c5c7f244cd06ebc73f2808195329ea69ff829410a6450040d50af363f
zz: 3d63a46a8d9ad4e3830175f7998bebb213bd3a8401b50cb6e2c42670356e9953
keyScheduleContext: 002ed6ef5e5a1e10b8ce95d98a132e9042fdb39eb661fa2fff03
53f29b397c31aceec26b8f681b7d42f5ce9979f35b851fd772d56055040326cc392f2a2b
cc5d3b
secret: fefa11bd4b906e90bae2c34db054d68c32428acd590d832c7090879027cc6d87
key: f85c77a1e881337552d20297e3200801741de39212c5f18cdb57062f99864f99
nonce: 2084a09dc1e85528844144d0
exporterSecret:
ca58ae00ecc470614f8839c668203a3bb0905a6441559b4f1328f3b20d15b3b4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2084a09dc1e85528844144d0
ciphertext: b706a7523384a553fb1c44d5d3186bb78484947cd17e72f15f1c83152510
e49680cac8f057f175187e94f18083

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2084a09dc1e85528844144d1
ciphertext: cdc1a9425ceea83e9f1d0a2be77525460cbe259d1a9314eba520c5f5f879
376a9ad7f8672ec943de425c6655c8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2084a09dc1e85528844144d2
ciphertext: 5bb2028896d91f156cd6e171d1470361bc07aa804a3ed64163ea67da67bc
e84e3d2f73b8d75f9a4dcb452b97e6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2084a09dc1e85528844144d4
ciphertext: 73973035d480c8299d1773522b738af626a5c834fc6af5ef5f8778fa6a76
7da89660f4aea7b4241b1f8b5cdebd

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: d2a61539bff0e4c64e88af0a3815b0269b78032f45d84fb82b6b5c0309f5cdd0
seedR: 6dbaa03c19b18e089416805b98b97e9be59b5b43348313f6c894aa749bd863ea
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: c4b91e87a49f07ae2b70020bc2dbaeba491de362b918db4589d1b64dabf3624b
zz: 32db4a665545350d97e322d68efee9dceeb8a2deff566762b89314b6d5519be3
keyScheduleContext: 01d2265ec86e8178427811787de22a5a66596c3a7c65806869a2
5166bce01ce008eec26b8f681b7d42f5ce9979f35b851fd772d56055040326cc392f2a2b
cc5d3b
secret: ba68621396bce80210a653cb6b7c6c53e3412587f2a3d359b5433717fe10ec1d
key: 0801b8427755e38ec575ca82c1a023976d1c6a05c962bebd5b711fb1e38790c5
nonce: 642d83347562610ba01a5986
exporterSecret:
5d97c23cbf481d5e7c9f5fe2ea1c4968d0e7512d01b81a2b897b80d5614c3d68
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 642d83347562610ba01a5986
ciphertext: be00a3d72559ea2091cf65a02a8dff3b79176a880caa47b214e75debbc42
28c8028a0eaa31a9207fdd595d4443

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 642d83347562610ba01a5987
ciphertext: e62e5472c78f6c88f40fbbcb9f41e89daf78c5be7ae963cc75ac9221ec1f
ffa7f112717074a635ee1a415e2a16

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 642d83347562610ba01a5984
ciphertext: 91d12fa708d5926578a7e9fa56a4342e0fa71e824908781d4c937a00163d
581fdd23af55d60bdb310289fdbc49

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 642d83347562610ba01a5982
ciphertext: c5ab4ff7fab32e3c6809b16bedfa2d4c72fc5f9b9061daa39fa3a7624d39
a797173c8e99649ef69b2362223981

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: d6ee4cfacf3ba765b5a8b6eeccb582eb5dff114865c8cc5dabf6f7c8ae173d0d
seedR: 9f6e9796f20a88e8c5887e50f152e064136969764e6e32389e8eea78ebf0f95f
seedS: ce0ba3357818e370eab3832a829dd5288638e201c8a00b6719d99bed3ec1f672
enc: 3df68fc4ccaaee084af119b988cd50d18f72992a7184a3bcd0e2b0589b90304d
zz: 2ca27bef5ce8b14e9480f9682bf7ecee181d3518c518e2a968d2ad65a186e3ea
keyScheduleContext: 022ed6ef5e5a1e10b8ce95d98a132e9042fdb39eb661fa2fff03
53f29b397c31aceec26b8f681b7d42f5ce9979f35b851fd772d56055040326cc392f2a2b
cc5d3b
secret: 0940b3fc4471901fd46e150287f576fdf679cb35ce9355bf0caefd00e4aba24e
key: 43c8db462fd0e25605aacc57639114f5c7db1333a6539fa0b9b068bce4458e22
nonce: 419e8f333efe8f64810bea51
exporterSecret:
2f5a9b5f204f64437505841208e952e65583951e773c4ba51a27adba6f96118f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 419e8f333efe8f64810bea51
ciphertext: 5cb775f56c42202bed1d67ac0ead881db3295d7ed2f34abcf41d2dcf3c6b
40bcee2bcd191aae8826219f0eeb54

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 419e8f333efe8f64810bea50
ciphertext: 17b380e3fdcc5c446a4033215da6baa26ccf86ca2812710ac5d0246af489
b35eef16107ab39507761b26494884

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 419e8f333efe8f64810bea53
ciphertext: 2c093b8997256aec1139498cf6ea920a7e38a80392a6a2860e502d7a44f0
2b8d9c648b1112d622d23f2b4a61e7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 419e8f333efe8f64810bea55
ciphertext: ff803471129292e117ec4fb05e93db8104f46b0faf8137a663a121c12503
dd8a5b0802c2b2f8883a9d93615d1b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: ebb6e3d16e1d36a2ab0573176c222afe150e50ea126473eec6b0c5e9fd718bc2
seedR: 4276d8976e15fd43ee257205337352f11b3454cc73f7a66963a84381ec977ce5
seedS: 54acfce7960bed685529f6e135ce9eae67d8c5e125ca296269d84eb1b65eb158
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: a1803ccf6b2a44513e02b2fddcb9aa49030ced3610f4d5eb6715bd8b9ad51333
zz: 1b0154acd11f266da0e70e48953c3e9f4732aa0c6a10a44171a309ff52a8cac4
keyScheduleContext: 03d2265ec86e8178427811787de22a5a66596c3a7c65806869a2
5166bce01ce008eec26b8f681b7d42f5ce9979f35b851fd772d56055040326cc392f2a2b
cc5d3b
secret: a0bf6443710d30369eced70bfbf7cdb9fe374478ad85f95d75f3e504815b9a10
key: eeb2d470a0c034af57e70511e0ced37dc354c4683ade1e093bb022a89fab5d5d
nonce: 8d67733e25a72e043b920f92
exporterSecret:
9e1fdb2b0ef7d0c26dff4ba52390f6e81d3748370b598bc93e8d0ef6d19df1c3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8d67733e25a72e043b920f92
ciphertext: 87f3ba9450a7e2390a34297659d297b262bddedadc9d17fa0a746c8ccd11
f5c93e58d4e9aa8b0af96cc7b84ba6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8d67733e25a72e043b920f93
ciphertext: b22c6c2554ad966ad3054de7a568de0f146b69a7efac7c60decf4fd541d3
e062efefbfb7d6dbfc57be689284b8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8d67733e25a72e043b920f90
ciphertext: 7c7c587a58ec45edf596b4df3fd72aa3b5d313b85596225c96038f36599c
42b34e8bd2ade51da9496b4fe0285b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8d67733e25a72e043b920f96
ciphertext: 1ad7b70f3dcf0c3b16c01b916afc18a53e0c7f16a93fe89336ee0e7fa55a
dd7e4aa61bcea06cabb5d9414c8c6e

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 2df5e86c1df01da4ad46e8ed41c74f099eb3c8d93f00896f70f49571305eed9c
seedR: fd8472c1450b15ae078be91f12b951149a851f4da782a0c0e9db19612990e9f9
enc: 04bbf2f400b2e54c85df0a5e342f13ca6d5879a8d4579edbccb6cebe5c6f43f4649
c2a9a54f181113f8c3c2349c8ffbd2e1fb967bfb95efe218f51db0cc346de93
zz: b404bfbf8f6acb91d51f6cf50dbf1d37acfe0f9a88628694f5572e4c6421bf21
keyScheduleContext: 00e0dcf00f27a233e6bc08a1289e07973ea4c6c2f9bd940420c2
a5d088f5ab42c6a6681b21466f477ed6d484a65f575c97c76db906c1d59a3c077b833a27
1c5f1f
secret: 86c8c6aab49eefd2813f0ecde8e81c1c8b7f17e75f19e35442c90ef4815c49a5
key: 48b9243d7a8f8937aa3eae2efa633501
nonce: 89f8032e5db8b3a9b3a910a3
exporterSecret:
841a22e061ea43fc64a35485230c88dff04df25b7f41098bd0c531590338a1bd
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 89f8032e5db8b3a9b3a910a3
ciphertext: a339992013bfb46ef084f698e4912c3039af55a491dde5e72219be0a35f2
cf38714dee46a2c95f6c981ad2bc81

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 89f8032e5db8b3a9b3a910a2
ciphertext: 9bd5a58920a4acdf6416eb9bf44b184a7f7a46ef91e731661fc9720e9900
91e3ba6feaaf2c3ef56802d9e0ec9f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 89f8032e5db8b3a9b3a910a1
ciphertext: b156d40cc31fc8ba33c31a5265475ac9301eddf908ba725e45de13df88e2
4af2bafde5da1b90fbafc1d648134c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 89f8032e5db8b3a9b3a910a7
ciphertext: 4a9c3f75cbf5790d11a26767b5f64902bfbc6509b210193761db4ba4171f
00e69dccd489164d0e6f2fd9a990f6

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: a14de6a6af07d0c99a16885bd373ee1e52b558a01696e2f1dc95518c27547734
seedR: 9bdc0ed2d5e213a03787e1fb2fcdf0c566ae3d6ea0f3d9ac58c6139f17e38e63
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 04b133250fe67fc7515f3bc896c805263748e3419a1bc27026c44f718254cdd0b05
9f1b183ec274f911f252f1b923487600b48fbbfd8121ec5c33f38719d85a17a
zz: ec872a7720c29868743a4ac497642b99d2f2949570128c716b8652971b41e8c0
keyScheduleContext: 0181ae34db4efb62b462aa17cb9d7a0b1986b1a404c76cf4bafe
3dec690d5d97fea6681b21466f477ed6d484a65f575c97c76db906c1d59a3c077b833a27
1c5f1f
secret: c5357fb9d30430847830fc1161af5e8b6ac877e5e26c7dcc7454687d192d0541
key: 2fc357b77491d0de800bbda785e865b3
nonce: b53f0b112c17bf32a0f95f23
exporterSecret:
776f756912c4d9fb82abb6c8cac99e3013f1f56d87fa9819ad979d773b28b7f1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b53f0b112c17bf32a0f95f23
ciphertext: 33d0ad0aec9d6a329efa8eff3d8dcb8c136549631212afcbbbee04b55a9a
ff35e112378c1078dce240685b189f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b53f0b112c17bf32a0f95f22
ciphertext: 3d28f40846ba302878bac52985f4ef08951c446abe1ab33ec38f7b6e8426
8a1fb857c01e513eadec3759f02fe8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b53f0b112c17bf32a0f95f21
ciphertext: 126e24d8a636680b3e9580d9418083f4845f4d97bc85177f5a57098b5139
dd0387d71b46b9a52a6c879fed9987

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b53f0b112c17bf32a0f95f27
ciphertext: a234b6c1c4efe8d69df543584ae9e6a876f001a0ec2ae411abdc5bbad71c
2016dae4d98e6c85c396abb512f5d3

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: f0e67ee793eb17e2d83c6c6013a2ea5abf8ce39df2ee20817253a453422cf292
seedR: 08fc3ed5e5e019a07abf59ccb5d887700cb39597315c68cea21e3872566fa0b3
seedS: 4938c3ad9e91da4812b9785cc621745d3942c59dfb5c69eff7074cbc1bae80b4
enc: 04b1b108178f1a8452ad27e700b6abbd64275cca5874622ccb21fe3983b5200eed6
dae796da4307ec4bbed5cb93a3fa911f8a7969fcf6c94b547f81ff91ee9dc68
zz: d76be19dbf9d85271f749f2d48d106345816b6a3075753431041c1ae419500d2
keyScheduleContext: 02e0dcf00f27a233e6bc08a1289e07973ea4c6c2f9bd940420c2
a5d088f5ab42c6a6681b21466f477ed6d484a65f575c97c76db906c1d59a3c077b833a27
1c5f1f
secret: 53f3bd7a851ee64688e82f4dc610c590b0dfc6c74b8f9ca111686f754104eb92
key: 77d7dbc6f09f8d2383b1f79cb42179de
nonce: 43b5709b9d143bbf988f465e
exporterSecret:
0b82772d4c0526df905e21d48f838cfe2fe7fa0d3cc2f28e422b63a794dcdc21
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 43b5709b9d143bbf988f465e
ciphertext: 3e6363671802325a9a84d6917e6a0960353dd2dbf41e295db6b534409a44
4037745c3b065a791684fc30ce93ef

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 43b5709b9d143bbf988f465f
ciphertext: a367b19b0c417b953f7784ec762990ce2b4b0f47493f2af9faaef67d84be
5c78b81fad29494404441079227d71

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 43b5709b9d143bbf988f465c
ciphertext: d4d5255a94c76bc41f3e5702f85802f53d296ee6ae68a4d496618f4cfac3
fe917f0f722a26f6131134e331e00e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 43b5709b9d143bbf988f465a
ciphertext: c0ae22f898bc7f56e94c31cda758a650b82275925880d434b1aa4dd3d661
b45e245378966e11b50da1b4c6c6ab

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: a638ed4a0e82c55c98689a83bc4b0ed03b9aee31ddd3b13e025aa97cbf0517ba
seedR: a01ceec0728863d3c573ce7e465b5e34f2ac6257629fff6a045b6f31b8f2ff1b
seedS: 863ce961c760889834b34784cfe7cac608beeca3ec22f35e7253cb5cd873bc01
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 0474f07529324c40599a765fbeea3f7f65c09da831463d11ce154fc41ff5317dae3
2266c7addec86c150f4679b799eb547e6edff592926322d01d2de0874fce293
zz: c2d1d27c6833a7e02d206a74260e49bd9b09211eea39b1a3f6ffecbc8f29342a
keyScheduleContext: 0381ae34db4efb62b462aa17cb9d7a0b1986b1a404c76cf4bafe
3dec690d5d97fea6681b21466f477ed6d484a65f575c97c76db906c1d59a3c077b833a27
1c5f1f
secret: 61e5daf3e0e4c4db3162a4cc5d990dd21cede0190174e2827b5d826e89505f59
key: 9ca74e9341d4d380fd8b57f03e2d5bd5
nonce: ba8393b301c837f56441f54e
exporterSecret:
25b2a4eb11c9efe0b974d0bd69bac1690550769cbe152c576b82b391168b43f7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ba8393b301c837f56441f54e
ciphertext: 26cecc37bb3b8628b5e3ae55aa252c4eac737c2248fc8645636f9f3c63f3
303414accc963885d26a444146c96d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ba8393b301c837f56441f54f
ciphertext: 0d7025d24c159ab7d63865085e5d8325d027481a862ec9ba46e0e46e081d
060109bcfa0fe905f046d1eef59049

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ba8393b301c837f56441f54c
ciphertext: ec2f30e4236ea44075ead7af40d443ae72d87df2434b4f8133de843c28de
a90d06c1e0a7077c84ab3a98aadf4c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ba8393b301c837f56441f54a
ciphertext: d405b7c8b38f94fd0a5b25b35dd530ed47340c2316dde471f60651f8dd54
07701e90046e367ff31dab104ae77a

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 859c4d4661cfccf02e8c4b75abde884bb08dbcc318b2e56acc4f595b81704753
seedR: b8cf55fff54a44eb4cf6f951e580405c03f72aade8474e8b6e86a7118d3f1342
enc: 04cfe80978baabb7b767255d3a196feffc4a77e7b09b45c19ee49d947c5036e33a2
54124d6f89d3d9368c42a38f3d0baa6bbdbb84b22406f5b1395e34d08602d33
zz: 8c59704a49eaf34699eb27b5016fc888b4be693890dbbad2b56545a968828b70
keyScheduleContext: 00e8c0e7b7e1350f45ba50f2fd8fb2e9bea10d5bd28e9cb917c3
adae0b6f8b19eee61cf47a1398afb2012077e2fafa0cf228d64ab9f22b63b07fb3896a49
5ce272
secret: 6229f2fd32e867b396a36f9ff548086f4915ddaa7628cb1af6fade352d7cf6ca
key: 38b214d8ebea4305d2ead33e169596228eb067147dc261816f952b33062f12c3
nonce: bf35a7db7279cd71b8664309
exporterSecret:
889d607ea5a873eadb3468063c554ad2ab5afe9ae6ae65559b51fbf2dbdc7c1f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: bf35a7db7279cd71b8664309
ciphertext: 658d3427e21bc7fba87cc10fd26a235e526eec111b805c16ba985359b910
29f8c8acc022ddd16265d981e8b452

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: bf35a7db7279cd71b8664308
ciphertext: 5fc0be104d84a79c0b853c5dfd1273b24741165446617e99356179c968aa
bb0094ab5d5bdda3d9fe8e5cf763a3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: bf35a7db7279cd71b866430b
ciphertext: 0125ccecd83a0f97fe18fcbef9ff3dd229b199f2e9aa15d649299f471949
4910c6213f3ca12b4a684c36955866

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: bf35a7db7279cd71b866430d
ciphertext: 5cc5dce6cb7858be2bd6f35443a006ffd527a03d13b39fe43242f6ec72e6
75b929efdf2c39caa989adeda00ed3

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 4d20e125e23418fdd9fed2377a109823d62696a7ac538097d6ff9cde7333b8ca
seedR: e247b41b5f35fcc6b8eee0c045903e3501c4435e61b9495121c4d806a5535af8
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 0486c02a28ac70f3ac99cc9476bd097839bf46068a63707972eb5e0a08a461f5841
e3051021735d371ab16674af4ada3eb4931d3b160b9e01068588c3d932c06c7
zz: 532f0da9ee52441d9541d69fe3733b5e9bbf4614702ccfb37f2481cbf5d12fd1
keyScheduleContext: 018713a4542d222c26d332326846e339b2247a082724788524ff
6a4eb9dbc23a79e61cf47a1398afb2012077e2fafa0cf228d64ab9f22b63b07fb3896a49
5ce272
secret: 5c38cceddbff3fbed605e22c8ae2b55eda874384f224f8321f0e0d4dfadc61fa
key: 17d653b3702094cb983571257564514eca6de37bc6d7dc94bfabc885461c54f9
nonce: 7af011ab27644b86060082ed
exporterSecret:
8a13a35e5f65fe72b9e44b1ab313acbb8ce33d140fd6d67f5783f96b2a06cea8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7af011ab27644b86060082ed
ciphertext: 5f3a98cf297dea317c9c46a5ca99d449ce1b37b949f20859b776b652b012
ec2306c11377a3a7e9b638693504d9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7af011ab27644b86060082ec
ciphertext: d7f76140fc09e177d2e69e79ae3b8cb8fbebb9aea64afe03f0e540c74e3f
056e8d8883fe3b4571570650fcee12

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7af011ab27644b86060082ef
ciphertext: 635028bfd49d41f6bbb32305b9e4b04ba9586d2a8f9f1a7f69635dffc82a
f7d3bf243cee2995b992b8fde9ffd4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7af011ab27644b86060082e9
ciphertext: 2b16063b4995efb0fb4e594bbccee4c056db445a5b8a781a6b15cef76790
e0bcfe907aaafe8aedb047dff8fbc9

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 60c8ac4057df119fd55487fde761fa1582f98e4293c0a2834bc818d270570ef0
seedR: effd0c0e02a3b9149a07708efadd52e6239f3d15867e3dbec69963fff77f48fe
seedS: e8af7d29c6da474f3815e9061851fa2651b00898870000ff27ec373d4117d8a7
enc: 0423653686046168ece7a52b8ae90b4759e98ae2d562b9b4f5bd9d67c037a495412
4d84fa4074bd1823a4bd1967b90fcaa64a301edfce48c46b7850e64a4104a3c
zz: 2b22a14ffb954acb4a2d366c318918026de11141d5ee55f1c3bbab843f156268
keyScheduleContext: 02e8c0e7b7e1350f45ba50f2fd8fb2e9bea10d5bd28e9cb917c3
adae0b6f8b19eee61cf47a1398afb2012077e2fafa0cf228d64ab9f22b63b07fb3896a49
5ce272
secret: a8d835b8b556ff5fa0e096868307b358d6b9e53f646d8fe2070b6fb8f606b420
key: a09e54a17cf1db07f2ab0788f8440f6d978796d087ea008cefe9a9ed22ee9a2d
nonce: fb4a23c48fa7e685a7d6e76a
exporterSecret:
106b5404cb13e19335c0c875ac2f080d4ddf83e87fab0e69742591d2c771171c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: fb4a23c48fa7e685a7d6e76a
ciphertext: e01296706f40181f5538c977cb61c83fc3cabffc02aa855b5e4f26a1f151
c0f28c6f7531bd9df252adf77c6a7a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: fb4a23c48fa7e685a7d6e76b
ciphertext: 01b86de4080d828e02e3e05273cd06d9e27dc506f313fba1def09d2b3a3b
3591ac1260f6fb100c32d875445c45

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: fb4a23c48fa7e685a7d6e768
ciphertext: 96ad1ea7d9baade04e9e10afc70c23e11c246be80e3a6b83403ff0e6ca60
90054f6c0e7740d6ced45560b94eb8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: fb4a23c48fa7e685a7d6e76e
ciphertext: 02f60d81bed2d51acd6b28d903e17ba7c6b7267953137b119dd4ecaa6f82
7f5ddb65fc16a6940aabb8e7a42313

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 988b9b7057d1231fbde4335f3bbcdcdac6eec0aa47809bf44e21bc7eada1e9cd
seedR: b8ee6bf7de2ba6fa4b1e17c3b4c7d1c4473efd04dedb57b51fc16da70e8bc694
seedS: 07906968002ca42b7e020ed5688888d6d39adf28bfce6e1676040867a44e30d2
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 04e07278d6acc2d11873fe0810c6fb2f428e10271b57b9fdfbd0d1f33add904fb16
753627b77df60b730bf50577d8c1d6402fbd4abc5c46a84dd8f27cc328c1e7c
zz: 80fe17e2d0a6fd7de53fae4ce3c7fd8f98f31909e0467dd8818b0e2fe8fb86f2
keyScheduleContext: 038713a4542d222c26d332326846e339b2247a082724788524ff
6a4eb9dbc23a79e61cf47a1398afb2012077e2fafa0cf228d64ab9f22b63b07fb3896a49
5ce272
secret: b9ffe6a3945361e1f03be9d00f3126a95cd34b6fd7c2ef5d382cad859010c6ff
key: c6f8a68c636353a02efd5163e4d643d3e8860a15096166c9e4a9794805dafa3f
nonce: 0825f842847edabba2b83b54
exporterSecret:
5e70f200d85c466fc8088c6362273190b7c30cdd545bed8f4905ada80982d704
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 0825f842847edabba2b83b54
ciphertext: 6f1b2bd7b94fc1eb19ceca585094e19de6b0c78d4a7e5ad6f338119cfdcf
ba48adef480e3768032e4daf56f1a7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 0825f842847edabba2b83b55
ciphertext: 6d0b86549862cb8d400425e924cc30b2121f5cfcc02c8fc9eca04b15e534
12edf811e2d15b2ed6601e73769a3e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 0825f842847edabba2b83b56
ciphertext: b3b2ee91f84de1be1db778227b49ebcd5226b9eab55b9b4eab73cb3214d0
2ee798e90b86d47d1becb30586130e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 0825f842847edabba2b83b50
ciphertext: 0eeffe74e03f6c1d4fdcbc84bdacb1ccea00ee2b139c5bd2f27b8870524e
39d9e428fa45a56eb87c4b7dd6f76b

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: dd6e705e673002e5c94e5b659feaf099c551f1728d7620967026c8443d48001da
8ce074df809d97fe06c927eb073824faf63f311d668c8e4491c1cc81d63e12acc69
seedR: fc3b1856d60632c6e9799c1f8a4b8add20ed637e24d0a0fec53e6ee58b55b318e
a403be8ecdbd080361963ab8a228803acfce7710121ac6dd59720444185c7775b81
enc: 04001073f3527876a5857e7a011acbb3b9d0b38f4783030cf233f1c558855c3de25
363c8cb58ec4d445d30ca28625ac3f8add94744df72343b41e663a98ead861cf9f500a85
d9b8cbebaa45b0baf5f0f7e996d6832fa309c2098e6d45363e4b60913fd1853597d9e8e7
9c5ec2d2474964aa6e497b42be4b056ece8115d3ac307a290a06a02
zz: f46024e7680e702f4fc513de6d3b106027e65403e798c9830b744faa504542585641
02f3c74db431505f10a8764ac8bac64f34fc4dc8f8f2834d711421c161f1
keyScheduleContext: 0031b1707e578c589d960c9e211aa23e80ed7fe6e9361b65be09
1962f9c84213e0d93df4d0e9f252cc30daba089600ce93e4c80425e21db501113eaf11f3
00739a2227566e0c425a324c9ec8639c51a8cbcd760aaf0176b6b7f8a06d80dad6e78531
3a099e0c1571efa8e7a038620d2daacee82943f29d6eea8361da9aa7f771d6
secret: 5ee8c136f812639497351658521f982bb6bdeb4d54cfe89c4b4ade2519cc1b36
033f26eec32f022275abb9b0e7a25c6fb88c72abb744be13cc9af1804f4b499e
key: 0f6b2e6e9d696571d9889ed8401d3f88e93df2f535b5906182fa5e7b84cbc19a
nonce: a391721e4955098083bb1ae7
exporterSecret: 4391300196396818b4e88976bd00bff473b652cf68eea0f7a24fb752
417d476ec92c7d1ccb84b8096ce45dde590f530298d16ee86ac98d38722c49e3bb508f1e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a391721e4955098083bb1ae7
ciphertext: 578e325476a1c9b47c5f035491ae8994c222203ad5240a655e72a822e29c
093c94cb5efab049a86c43ac36ea05

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a391721e4955098083bb1ae6
ciphertext: fb7d85b6485014ddb9c321f63fc474ab51bea80cb055bf2fb5b0a4ec464d
23ecca8e1dcb2376a4222f51a0fbd1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a391721e4955098083bb1ae5
ciphertext: 979936bf5e76f02031f47c1700f0a3ce05c624341c85ada26b952a24a1f2
c6aee62255e5111503baafe2d00668

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a391721e4955098083bb1ae3
ciphertext: 2a1590599a5cfdee61ce850865e7279407572696fcc9b92938e35da4cf3f
462e9579b3946886265427d4e7bdd8

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: d31e42fd27084475953b3e1ced1f6db8395467b5ac15d440c0485f1bd6822da20
87a6c4cdf6d251a47f85b4175f7c7fc920ec78dcbbb1c1a0633025095b23104f11c
seedR: bb3691655168b474a874554b92b434f124ad6b1c67612287be279362ba4113d32
e8d8fd018072ec05d028c987506876945d16764b2c9d9291faa19dca77ed5bacc2a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 0400069a9efaa43ddf59f2ea683b8ca95d50f180875cdeba520660a10b946ace183
c2bf2a74f1b5fe6ec29513b565fdccc45d56e736b1d56207ad37a1b874bc72d9f1801118
54b81703909791e27dc829a85d24e8a971ddc4ce75369baaeec8f9591796e544ceace77f
8da1e61ec906e4ff3be1437ff03d0147b30706730990b25361a75e0
zz: 766f6350e71360de43585dabb1f09a87181763a047e40587e0c9e39f26595c51dc66
e824b6717297db62f73ceabf1ec71a5fc4456adb6dd141135507f2169c9a
keyScheduleContext: 01dc74dedbec9f7a36503b6c263059c9a11a79e4670a12bd2452
69d81c85a0feaffcf1b23b0748db53bb52b72eec5935e174a97db18d00f324ecdcb45295
660a092227566e0c425a324c9ec8639c51a8cbcd760aaf0176b6b7f8a06d80dad6e78531
3a099e0c1571efa8e7a038620d2daacee82943f29d6eea8361da9aa7f771d6
secret: ccb20e86ae05a432c2f22963c89a403a01b33f4a1d4a02f0da2fee0e813cd3d6
372fadf3fb90307221c50d46042196f537510ba37338cf7681e33b7e5eacce88
key: d2303f1fdc620e3577e85dac2ac76b5e5e66a9be2b07b353552587f1bf17dfcd
nonce: 601c3f5c01b69eee6c273aa7
exporterSecret: ed44e02da7e1aaaf00b678cc2982823f974ff2c6d0ecb1ac6e176928
34ab8826e1e94ff0f54d07703e490bfb5aca572e6fb0d8c938e126efa36bfcac1d97a8cf
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 601c3f5c01b69eee6c273aa7
ciphertext: 93814c57b802da5404225d38c9b78b64fcd29b0f332501dca6765e74a85e
7ac6bddcd55c82e741d172251bbd6d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 601c3f5c01b69eee6c273aa6
ciphertext: e2144f2b780e3b9cfb9f1a50cfc6dfabc71c5030184668ede14be3259b02
d0a6b96c8ec99408ccb57ccd5ba05f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 601c3f5c01b69eee6c273aa5
ciphertext: 585e1a1855856c32d2c1dc9ac2a71db03e0f5ceb72e15443195c226456db
4f1374dde2913ba961acfaf154f9cb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 601c3f5c01b69eee6c273aa3
ciphertext: edaf9feb5d6081ba123b3fe891ba3d8e10d2161cca205b04ea7405357e50
0354b0984cf9f6740023bee0e71b53

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 9f59abeaa47658a5803e02dec0920660e31b08b987d3e9ebb0976a4dafa6fda5b
8f05610ac2c22632c2a5205ea504b12f896074d8b575d1af7dc1b056c4606302199
seedR: 1463b22bcd9c86918827ccb4997c26b9d53f6dcc81183989b81bb86f0c494eae2
888d2d27dd350332471799fbd63e47af14ea4e3aa4b751f91da32e14b8668e5d54e
seedS: 5434fa30107088f247e33fe1b8f1453ec5b80222bf39dd500d3fe3b21692490c7
d5f76ebec5664299ff029c447517c3769c0d93abfcfb02758f4576400ff9b4adb46
enc: 04014c24eb4dd68f75e665ae3464807088c96cd968aae391177049f9e7071859555
7da6e315c91ccb0bf8d1683e7454acf292d94705c5ff8993e6179e2fac3903753c400585
62f4a0b857135a5678d718c4f341c46b8d2d61c4a9e6b9d7391b1a4d4e37db73a907874d
03b8a4906a8978426e716d7f054ea78c6c5f6238e057814aa00d7ba
zz: 42a47e9144cd6e466b6e384d92f75eb57597f47a33c87ad4daadfc10f345e49897a9
47adcdf804ee8dcbfe878197e802181eee1367ab7b349d1a8b5ff4444f98
keyScheduleContext: 0231b1707e578c589d960c9e211aa23e80ed7fe6e9361b65be09
1962f9c84213e0d93df4d0e9f252cc30daba089600ce93e4c80425e21db501113eaf11f3
00739a2227566e0c425a324c9ec8639c51a8cbcd760aaf0176b6b7f8a06d80dad6e78531
3a099e0c1571efa8e7a038620d2daacee82943f29d6eea8361da9aa7f771d6
secret: b72b53c4d6f9c32137afdcc2622c491475eb36713acad5b6f4dd3093798289e9
a6aaaeb1e174d3398d25bd678e0ddcadd2a97ae47e44065034570ce34876ed9e
key: de6efd0bd35add5381ebcd61e054d47a4ed8a8c781adba21f529c6eeb367375e
nonce: 4d46b458eb11975de36b5d28
exporterSecret: 7f10cc2f8ac59a785023ec945f861eeebc119ab8f78e946db4d09f03
80141526170cb640e13679e141c242a0fce887fea6cb182854a30cfb0a8f899ba030bef8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4d46b458eb11975de36b5d28
ciphertext: f8b756d66cf04835114ed82d0624d3a6a591108d0685cad9d31f9afce3e2
b437be3acab04cd40351f319944ee8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4d46b458eb11975de36b5d29
ciphertext: 30dd97ad75e13ed76c9ac2fe66f1f7333070532744e291d4730efcbb486f
58702b108ead631843e8216982541a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4d46b458eb11975de36b5d2a
ciphertext: 54d1146fd0aaf20916b3d4c6db54076fe6ddd91eb29b895c27e58075fbef
da2d6b0cc8ffbd9be766c1167719c8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4d46b458eb11975de36b5d2c
ciphertext: 4c065e11b3862704afbc026001653798ba49d455dd33fbad81195c67896d
32ef9fc859f8c519a4185e849126d0

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 73ba1253ccbbd30ae850c55e0e3faab5d8ad03be092b9fc29b1958bcc10ce8293
b9071368103e28a2b41eacc7b8d826b8f7edc193c121ff5410b60a31d68aea74f55
seedR: 61d7bec5cd139d101df42e03fabe6f7810b89e6c73495dd85adcccf0f87ab0074
4cbbd233a421352a48f4a078a42c882d98aa5f9dc7fe16d4f0633aa7eed7fad6d6c
seedS: 87037aa1958c47f24062d8cb32edf298f7a45abe81a930891977fc59ce15c766d
784bffc400651ddeb49e7cf3c682b1f3bbeb6a6e5417c8ea78e426ba7874ead67db
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
enc: 0400bfe56b4c738593724849154dc503675c4bd54fedf881dd5ddebd16ef026a86a
4970bbfaa243dd9397b4dc364875c5766d9fd8b69b400ca1d528e6c09f57e3d854900d97
8fb363e0bdababf52c9e11a16aefb04a8ffa6ea4b67913784ac01ca72fb32ea9c2c54571
a02e071ae35ca3a63c3b33e8a8c18f303250f30fd6ec28e20d9c88f
zz: 509afba7e787893312cefcf3ec155b0863707ae22127e62807e6022e79d306fa4db1
71e822d504cc552c3c6e5caeb28f391fa9ef4087f713e2433cc684de32b4
keyScheduleContext: 03dc74dedbec9f7a36503b6c263059c9a11a79e4670a12bd2452
69d81c85a0feaffcf1b23b0748db53bb52b72eec5935e174a97db18d00f324ecdcb45295
660a092227566e0c425a324c9ec8639c51a8cbcd760aaf0176b6b7f8a06d80dad6e78531
3a099e0c1571efa8e7a038620d2daacee82943f29d6eea8361da9aa7f771d6
secret: 85de2399b07f57a0017fe3a302ba65be4fda12e7aa27888d9404f6f133d398f5
b48d3ab276b0a59043476da4fd0048d5955cfc8d589d0c5484aa62f2f43d843f
key: 42ea571ac39e5469bbd03578265089e3ff00222a337db8b5e37b7267624d32e4
nonce: 04f4e49ae4a880bc7bfddddd
exporterSecret: c4df767f335de8bbe59252e312e4d3cb66789050c51c7dce4ef55232
311cf9ad7c02750c05eaf78491e01bc6ea08256d42bc4f9167d284484951819836244aba
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 04f4e49ae4a880bc7bfddddd
ciphertext: 3404301ce6c21a7c48e354fc45f962dfd6ec99f7fd42ac235fbc4c542854
f9849d60829290d76b785691c33c25

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 04f4e49ae4a880bc7bfddddc
ciphertext: 5c92917722cef9831726b376e4d869e7e4eeb0d759fc1386cb668ee49285
00c1738e847862519258a094c44cdb

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 04f4e49ae4a880bc7bfddddf
ciphertext: 8a018a7d01e378ef2f27baff5ab50ad75e2c67264aa84f33d8161d429e2a
068edc7b91b628bf28f3d3fefe3928

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 04f4e49ae4a880bc7bfdddd9
ciphertext: e2a140f6f88f7cd2416af37e9573042e916e7e2778540e97b74de8a9f00d
9e16b35e3107f6dcef3c6b7a70f357

~~~
