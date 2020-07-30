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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/580119bb7bb45fd09a1079b920f8ef257f901309/test-vectors.json
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

For the variants of DHKEM defined in this document, the size `Ndh` of the
Diffie-Hellman shared secret is equal to `Npk`, and the size `Nsecret` of the
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

The primary difference from the base case is that the PSK and PSK ID values
are used as `ikm` inputs to the KDF (instead of using the empty string)

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

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
any other identity.  If an application wishes to authenticate some
other identity for the sender (e.g., an email address or domain
name), then this identity should be included in the `info` parameter
to avoid identity mis-binding issues {{UKS}}.

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
PSK: in scenarios in which the adversary knows the KEM shared secret `shared_secret`
and has access to an oracle that allows to distinguish between a good
and a wrong PSK, it can perform a dictionary attack on the PSK. This
oracle can be the decryption operation on a captured HPKE ciphertext or
any other recipient behavior which is observably different when using a
wrong PSK. The adversary knows the KEM shared secret `shared_secret` if it
knows all KEM private keys of one participant. In the PSK mode this is
trivially the case if the adversary acts as sender.

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
seedE: a77ae3e14cc2ec9e603a9049423d48e66a5e3139e896e95cf19919430657adc7
seedR: 1289f0db1d8f68d0c531b5e53a40911a2a2347059355d7c267717033fef2b08c
enc: 8a07563949fac6232936ed6f36c4fa735930ecdeaef6734e314aeac35a56fd0a
shared_secret:
f3822302c852b924c5f984f192d39705ddd287ea93bb73e3c5f95ba6da7e01f5
key_schedule_context: 000c085d4e6d2e6a568b5dcf334f7badd56222cd79f2ac98b6
f99059f311c3f16a44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 98a35c8191d511d39a35afcb6cd4072d5038afb2bcc1ecb468626466b2870447
key: 550ee0b7ec1ea2532f2e2bac87040a4c
nonce: 2b855847756795a57229559a
exporter_secret:
1aabf0ea393517daa48a9eaf44a886f5e059d455988a65ae8d66b3c017fc3722
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2b855847756795a57229559a
ciphertext: 971ba65db526758ea30ae748cd769bc8d90579b62a037816057f24ce4274
16bd47c05ed1c2446ac8e19ec9ae79

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2b855847756795a57229559b
ciphertext: f18f1ec397667ca069b9a6ee0bebf0890cd5caa34bb9875b3600ca0142cb
a774dd35f2aafd79a02a08ca5f2806

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2b855847756795a572295598
ciphertext: 51a8dea350fe6e753f743ec17c956de4cbdfa35f3018fc6a12752c51d137
2c5093959f18c7253da9c953c6cfbe

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2b855847756795a57229559e
ciphertext: 2e5fa3a358e3ab64e5e981c4b89b5ae4cc5b800aaf726dc64ff857536a3d
b0e6d816199e711aac60c4670c2a31

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 0fa1407ccee05de0cceb2f2d2381d2df0602dbd43be90eefd288ce4ad0b3ba32
seedR: 326ee379f778718e6cb343f55668fbb9d0098ba0503cd4414a8f1ce252605c39
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 08d39d3e7f9b586341b6004dafba9679d2bd9340066edb247e3e919013efcd0f
shared_secret:
9d4fe1809006b38854f056830b8900086f562207dce6010eadf23d2d5303cdf8
key_schedule_context: 01512564fc13bf3387a7d73eb72eb6b62766480582bfe146c4
e5afb8788652269644c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 84d1c77bdf45e43e2e84f607573f0db0758c56f322500a673be8e2062d343b1f
key: 811e9b2d7a10f4f9d58786bf8a534ca6
nonce: b79b0c5a8c3808e238b10411
exporter_secret:
7e9ef6d537503f815d0eaf70550a1f8e9af12c1cccb76919aafe93535547c150
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b79b0c5a8c3808e238b10411
ciphertext: fb68f911b4e4033d1547f646ea30c9cee987fb4b4a8c30918e5de6e96de3
2fc63466f2fc05e09aeff552489741

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b79b0c5a8c3808e238b10410
ciphertext: 85e7472fbb7e2341af35fb2a0795df9a85caa99a8f584056b11d452bc160
470672e297f9892ce2c5020e794ae1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b79b0c5a8c3808e238b10413
ciphertext: 74229b7491102bcf94cf7633888bc48baa4e5a73cc544bfad4ff61585506
facb44b359ade03c0b2b35c6430e4c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b79b0c5a8c3808e238b10415
ciphertext: 5aeb09a3798d21dc2ca01f5c255624c9c8c20d75d79d19269eca7b280be0
cb7851fae82b646bd5673d10368276

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 02900cb4856b5f222293a9bd7bda2f1f81c562dc3002336ad1c39f6572402b7d
seedR: 518df90f0f5044ce653180c700e4902d37a7ba1cd23482a76e18b300fecaac4e
seedS: 262a05ad0c08030cdbbaafc03d64f33b95bf8089f216c62ac39b72064a4b4dcb
enc: 56a21e8b5416d187c3d865765794e7f361d631049ebbb6a64ed28fd071068121
shared_secret:
dec9ae331e9017669151e07c06d1cd7f3dd318c180c9cad5223e1c2b019d2243
key_schedule_context: 020c085d4e6d2e6a568b5dcf334f7badd56222cd79f2ac98b6
f99059f311c3f16a44c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: a78ac3f106be621d7ce48d7f02e9c69f23c042912697a985787c34e5340ca8e7
key: 82a24b8790521d6b2d260664d9bfaefc
nonce: bb0cb3a72dff841c796fce56
exporter_secret:
933d7ef819b2fabc810db31f7fcbe5b16c4efa0f4b715e888466829d9b22062d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: bb0cb3a72dff841c796fce56
ciphertext: 86dea722bc4f4cb0983b70dbdb539cf79e393546805d90d3f832af5f907c
86f37ac579976db191a479c9450f37

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: bb0cb3a72dff841c796fce57
ciphertext: 4f6b757fc0e807cf8f4726ed1bd05c6b87714b2332372795f7e8579fe21e
104ff8180fea797855a62f71a37aea

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: bb0cb3a72dff841c796fce54
ciphertext: 999285da95ed93dfb48bbe99d46ebba43c98e35f6ccd4fed92edf9d618e9
8174b63a0a2c12ab91521669fdad2c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: bb0cb3a72dff841c796fce52
ciphertext: 1ac6af74dfe65c63b046eb99fb9036ce759ddf5bfb3a396796892c78ce3f
35beeedb7b3d1b515a9dff7d9af365

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: c1d1028243a951dbf6469025f3a1304407b08fb932104e61c7aab42ab4f1995c
seedR: 02a965d8f53bbdcc11cc618d4f31f69277500b75959ca97fd533058315511d1b
seedS: e9c09a3e50073935e75d3846007a26088a93ebf58ad0bb30ad6c42a9d4d2419e
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0f496b65ac352457865d9f6cb30e0ceaffee742accb016c2c1a7cec68a33244c
shared_secret:
83272c7b992c197f882d992ef6737bb7f4b17ddf103368e1d7e90b07c946b2e3
key_schedule_context: 03512564fc13bf3387a7d73eb72eb6b62766480582bfe146c4
e5afb8788652269644c484c33962433c90728ac6c2893f828d58cebf58ba4fdae59b0a8f
7ab84ff8
secret: 619e4c000edf5cb8c2b795fbf2dce842d0ff5cba4e12312f5fc67510eb059560
key: b305d06827e854504246d9bbae3b1f80
nonce: 4940e55b734bbe1d46e24bd6
exporter_secret:
bd6ec34885e97fe0c07bda3454d47ece7b6e9a1a05f729223485e4335c40cbdf
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4940e55b734bbe1d46e24bd6
ciphertext: c7200a5246b4aa9e6878e22830d19466ca31394651ae84383f183991d3a8
662415d60e1e073209e6dadd480ff2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4940e55b734bbe1d46e24bd7
ciphertext: 8071f54a0a43f77a30de1fd96133d91184b5f863525d7810eb9350aa2555
8bc470781e62c27fe9a566f15efdc8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4940e55b734bbe1d46e24bd4
ciphertext: fc9747b21f74c098899e408d86c11d28617a1a3eb2d985fe4af7ccea2023
43df096920759614bfa2586f0f1c5a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4940e55b734bbe1d46e24bd2
ciphertext: d85c2d06220ae34064210c4129f8c95dd43c45fb87ab25885467dc2c6a66
3deb84043eedde254968c55ef693e6

~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 8c5a8a722a10c144a7577a73bbbbddb0284ea3436f9901a12c54eafd6eb5cb81
seedR: da0002ddf1803c7d54c1fb10fd68eb76afa2aa4577352b9ce26462cf63a97f6f
enc: 716281787b035b2fee90455d951fa70b3db6cc92f13bedfd758c3487994b7020
shared_secret:
f995f043efe63c77ac333fbe6007240fd01006bac1b075d2807845afae89a19f
key_schedule_context: 00cbe688614d6e54c26594f3c118e6cb1a01f6c6572a9112dc
2687bd3e8b1e6ba06da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: b061e1b7e604df2fe8a4d32e25d33aeb5a0849e7b15dd212231adbf656259f8b
key: 1d5e71e2885ddadbcc479798cc65ea74d308f2a9e99c0cc7fe480adce66b5722
nonce: 8354a7fcfef97d4bbef6d24e
exporter_secret:
3ef38fcad3a0bc7fca8ba8ccea4a556db32320bca35140cb9ee6ec6dd801b602
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8354a7fcfef97d4bbef6d24e
ciphertext: fa4632a400962c98143e58450e75d879365359afca81a5f5b5997c655564
7ec302045a80c57d3e2c2abe7e1ced

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8354a7fcfef97d4bbef6d24f
ciphertext: 8313fcbf760714f5a93b6864820e48dcec3ddd476ad4408ff1c1a1f7bfb8
cb8699fada4a9e59bf8086eb1c0635

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8354a7fcfef97d4bbef6d24c
ciphertext: 020f2856d95b85e1def9549bf327c484d327616f1e213045f117be4c2875
71ab983958f74766cbc6f8197c8d8d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8354a7fcfef97d4bbef6d24a
ciphertext: 5e688918b05e96631628eef3e74781caf41c4f25ee1ef52ca1d746ca3156
1392c8833a7232036bf8e839a4c8e0

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 31c63611a67f55281f76477958758873f7a65113f3e1666ba5fce96e96852684
seedR: 2dc8b23353f632c2797ba4644fafb7363d958c1fce79162a215863951bd9a06c
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: f4639297e3305b03d34dd5d86522ddc6ba11a608a0003670a30734823cdd3763
shared_secret:
95978c18311fc9e360209dd2cd10b2fcacf019ed25f7703cb2b4e4538558c13f
key_schedule_context: 01f5f7e2ba59c3ff0cff51f71c4204fcfc76c95f778b37ccdc
6a83b3df36c33e7b6da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 2c25a1d6e3b889cc8ea031a96aa3357f16973f83ab1d444114e7bb4f56e4a639
key: 396c06a52b39d0930594aa2c6944561cc1741f638557a12bef1c1cad349157c9
nonce: baa4ecf96b5d6d536d0d7210
exporter_secret:
96c88d4b561a2fc98cbafc9cb7d98895c8962ba5d9693da550cf7ed115d9753f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: baa4ecf96b5d6d536d0d7210
ciphertext: f97ca72675b8199e8ffec65b4c200d901110b177b246f241b6f9716fb60b
35b32a6d452675534b591e8141468a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: baa4ecf96b5d6d536d0d7211
ciphertext: 57796e2b9dd0ddf807f1a7cb5884dfc50e61468c4fd69fa03963731e5167
4ca88fee94eeac3290734e1627ded6

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: baa4ecf96b5d6d536d0d7212
ciphertext: b514150af1057151687d0036a9b4a3ad50fb186253f839d8433622baa857
19ed5d2532017a0ce7b9ca0007f276

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: baa4ecf96b5d6d536d0d7214
ciphertext: 6232e4a184dbff7361f9e4d6bfaaf97631225ee317e63cb09e8f74fc93ef
eedb6385d4f4cb2e30ffb82aea0e1f

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: c9c2d6f5a6f88e4c2bf5600817aa140fcb46dc682942bfca357c30fe2db17d6b
seedR: 71237558db2b55c1a09f6695187d2af6e7d1dd97256cbb927bfc8a794476d07f
seedS: 4255c61730d15a7ed2018a023ad45274c1ab38ce621d4b597636e08e97619ef1
enc: f82cc290dd57c0c63f041ad62605d1ae0c5436243e18758b2b63658904ee6a09
shared_secret:
92d03a5e87f58fda583129e62f1cb55769df02a2453863b0a09f55e4bd5ff7be
key_schedule_context: 02cbe688614d6e54c26594f3c118e6cb1a01f6c6572a9112dc
2687bd3e8b1e6ba06da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 4760feb6cc5ac6891ef2114490723c6ca2ad3352b2c52a60b390616d731f7767
key: 7638c7ade5856344fbc3a92600fa278dfff1c22b5857fe2c391e5bd248ac32ac
nonce: 1d14b2320b54376e6c43e791
exporter_secret:
0ea20eb846e3c26f1ee8b2ecf55c9abdfecc910387945528c73a5ff91bc4ef38
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1d14b2320b54376e6c43e791
ciphertext: 30b013196168dcaf7a07047eda596f8c4f425abe6cfa269a7602b2a2b0be
a958e2ded3c68c8c9e341ca4bf2e31

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1d14b2320b54376e6c43e790
ciphertext: a259ce67a35c44ff9616f83cceadb2f0f542b208e9410686ece7e3eb92f0
8ca2e3fc95ccde64e849c96367952a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1d14b2320b54376e6c43e793
ciphertext: 4691caf957cf159e39a3f66cee9cd76e06ae3e7f97c577898423babfdc98
00669d69356531dab839e0a491d502

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1d14b2320b54376e6c43e795
ciphertext: 471ccbb6a81a3bfcc4c11dbeed62e95a7279fdab214f3b0cf22e998a89a2
fd054fdf6326ea6a340b20cfafae20

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: ca35fe19e214033e34465a3bb125dfea8b483e55fb8163774413d95a4d9b1f0e
seedR: 9a063358dc95c04f2bdf2a9a2911145c0632f49012829d92b2b5d9f398a9cbe3
seedS: bc7c6a9ce74ba9e7fff0644da70899148f4775eaa1857478f0275af76cabb764
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: a6125996b3bb128bfa05392ffb39afd1e5b0031625e26c8c484e4aea0721ec39
shared_secret:
0c9ac657691ef63b088f9777e84a9a8ccda766f0c9834ad318c0e49cc34fa43f
key_schedule_context: 03f5f7e2ba59c3ff0cff51f71c4204fcfc76c95f778b37ccdc
6a83b3df36c33e7b6da3f8f29fa93987a2c185c1c17e719f7ae8eb4d564b80119e012c9c
959b0ca1
secret: 502a94d9ee9cf5367beb65a97e7bfeae19a7cfbff25c6a4d2a9d1ece4d744b41
key: 968ebe599b1443cbfbd1914daa5bf667a52cf7a3339ecb209e8684f1f9c97d86
nonce: a0bcc93f25f5b9e707f453e3
exporter_secret:
12fa76c18f0c16769262574bc6d49e9b22cac1d963e3e6b91031f61ef4277350
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a0bcc93f25f5b9e707f453e3
ciphertext: 1b049559f757b7c16d77bec8a8cf9c1cecc6becaa08aa513c791822b8293
45cf4477936df226e34804acb93b33

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a0bcc93f25f5b9e707f453e2
ciphertext: 21311cd102acdb30e18669620623c54dc66eb0c5cc7fad1ac1a327062d89
fc1fb6cd1228f8de48418d089a709d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a0bcc93f25f5b9e707f453e1
ciphertext: 3e84e9e5c3d004a6d8cea022c8ae5a10bac7d75829a189b137db55e6a5c1
1974792e8a6b92cc208d615f424d45

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a0bcc93f25f5b9e707f453e7
ciphertext: 595f2004a961c4762e418d33821f5c73335a681e75512134c5a5e3912d24
bd089b074e018f042e6164bc72c5f5

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 616ed5a6277fd3324e0cc0f4349cd345b0adbb1ceb98de44c03aab083fbaa6e6
seedR: 67bc0b8ba01fd8a1526d13c803d4d9ffe1a9914ac27e7a6c925b1580893a8485
enc: 048a0c9b27c844f5f1c6a1d9d570e34909c6359997b6acbd8132f1536d1f7685ff0
d203f205dfe4a789e4af3f599172b613d060c80d0e1341f066a87c0f83d827c
shared_secret:
5f175bec391524f0153b05559212adbc2f5d6981b95a5d53fa7ed58fe5e156be
key_schedule_context: 00c14ae6a0da7c6764c62eba270ec0cc28b5b568b4849a9b59
425c08860800fad8a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: f753e6728460efed42ca308bef93e8b6646cec0252a0154d8310984445bb0629
key: d0696b5461fee5620d54f33b04a00f79
nonce: 99f33bd3ad9ad334b17de055
exporter_secret:
f79e9a0e83b5c678cc0c9240b68fc3a84096ce374f37673ad4ea345ef0a3510c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 99f33bd3ad9ad334b17de055
ciphertext: 0d77ad2340cc7af125fcd7f4ea63bca7e857d774d08365eff8c7f63091a5
e5aebca4721c854579b11149649209

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 99f33bd3ad9ad334b17de054
ciphertext: 90260e86b560860d0bf7bd1273bf7b6f4bf43aa94d475c93015c5d5b536a
ae7631227968ab1aecc337cd080988

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 99f33bd3ad9ad334b17de057
ciphertext: fba616306cbe53eb8faef059a8d39947102a037c2e5bfb6b770bf7241576
b74e197ae6972c39177b8393e4bece

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 99f33bd3ad9ad334b17de051
ciphertext: ca7c1e359bb916ec8aed3a10bd2a703d044af6a1a1b5a8f8bbba63141f35
ca7c292516bda6c97c4bfe85333f6f

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 8131f719cf2d1f5263da51e133876a99eaaf5d5fb118bda64ef12ca6fa40f987
seedR: 236ddc165201cb79b2d8c7399c7f6e6e8cc4542b2fd1b75d107875db2b89cced
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04df79d22d7cba95ff448cf84ffa01cdd87a68c9ef70dd926fe164a76d2cd243036
f3a34e9bac0725406fcb46d7c723248e42c3b329bed5bf8fcaa47d87d9d3e00
shared_secret:
1f245a22765eaf94b3a76463b9a248941078d138c3216acfcbd1d25f8772afda
key_schedule_context: 018c27d3410cb79f908302ae06a67ad4c6f971cc37f64c2380
7cb4de4adeaa7d76a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: fc6a6aca6b179515d69086844efec0acda07bd55efd50873cb46fb811faea941
key: 89fb75a38ba6bab89b1a8b0fc7db366e
nonce: 00b1c2de64b6a56a51921d56
exporter_secret:
cbd0d3b0ce32cc4ad834a0e81cecd21ecba042a0f4f25ae839a1fe95e56b89ff
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 00b1c2de64b6a56a51921d56
ciphertext: 75e82c5e991af745c380557b2f03f793dde5f4a78b3bf31429735aebbbd8
81580917e8a489fb0da3b081444319

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 00b1c2de64b6a56a51921d57
ciphertext: bc7e436c6435634a69147dc20e3abae51f2c02f96ec2b198138b5e10e284
20cb45a7ee149b1d936154ca320e08

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 00b1c2de64b6a56a51921d54
ciphertext: bd020f02b8eaae481e512bfe4969b2b285c636f756c72d70022f31af52bf
00692c57264bb214a412ac8fb1b965

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 00b1c2de64b6a56a51921d52
ciphertext: b1ff4e7b8ec452aff36b06c5c1bcf7e4e1cdd3211f1516ce752366f1b81d
5cc813e4d5e2142239afcbd1a75f4e

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: f9b977313fa3cd4dd8637307fc93e48093ab6bcd45781ad9f7a79f5f0e379bb6
seedR: 740a67dba29760f8d95e953a1ae75fda6d5eede2a41c15f4860b5557d4763fbf
seedS: 174deda86fb885b78e5ef8ad158be3c38349c5322120f03ee9ddb6336788d8ca
enc: 04686fc26c925890636fdaabae3434af53172035f7a191bc21fbc7ad9161ee1673c
0e6b61d0c4b2db3140d622c46c8e42fd4e10fb48b4fd522ff59f795659a5b13
shared_secret:
8e1409be7adea332a36fbf29bf8668ae13d66cfecf5d02e8d2cb2c16950af36e
key_schedule_context: 02c14ae6a0da7c6764c62eba270ec0cc28b5b568b4849a9b59
425c08860800fad8a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: 35cafa2133584ef110a63010be05bcbc32fe5b5985f5b62ae94c07cd3a844ae1
key: 40eef365aa0dcee18cb7d16b0d24e35d
nonce: a5f0d2f22f3e404976ca7b1b
exporter_secret:
162a8e2af6ba4e66e110b8dca44a076f49d4fba4614540341f4013159eab5e69
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a5f0d2f22f3e404976ca7b1b
ciphertext: 1e9233f2b21834f72bc2b23173b107770d97092d1fc57960aaf0d011b1bb
8f1767d6ff8cb3b5bdb857168260ee

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a5f0d2f22f3e404976ca7b1a
ciphertext: e870727eec0872dfc176e3d48e894a6fd23c560b2f7c097febd70cf81971
0e8a0c30adfe0a1d740b5e42d09325

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a5f0d2f22f3e404976ca7b19
ciphertext: 1b28bcf1c88146063ca68a999bee8b6d339bf9ec9ce1b22aad255abf96b7
951f0d14db39d2a7042402d2ff3b41

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a5f0d2f22f3e404976ca7b1f
ciphertext: 10ec221a706669d206e4fdaffe72adadf4c98286728aa58b91ffea203517
9ecf97677723a814464d6c0e3220f5

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
seedE: ac7928bd504449496e56517f59ad30ba62575c3c328864340247d73217823bb3
seedR: 85c7ca573ca20cffc0db7748f2b93a1faaa951aaedace61a6cc0b15755cf7cdb
seedS: adfa10a0be028fec577fc0d8da73b3af3f6c8d96976ac3664b1a191c8ef0506c
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0435ea0b3e1693ee6c10ab35b0d6a01d9c6879be1ca8676cc2fd16e94b622368b41
25f4528deeb1d32dbb0a9b815341ee6dc723e00dfad789a46abc337c0cb2d74
shared_secret:
acabc837f0148300e7264c7bfc597ce119a5a77c51eb091fb943573cafa69ce2
key_schedule_context: 038c27d3410cb79f908302ae06a67ad4c6f971cc37f64c2380
7cb4de4adeaa7d76a633c96fae27707d2cfedac544e900a8b52a016cf86e4bf25a7d350f
be847f8d
secret: dbbb9e2244449b76d56b48a7c8257f8b03e9a5948fc382528ad4f8464f3b8ee9
key: 51ad48b07edc1bc355bbd8ba1288f90d
nonce: fa9f85cd9f4e97cc5655eeee
exporter_secret:
25fa7177ee5c4686f095fc5c51d2ce5c5871a6d1210c3e345fe4ba2fc8febbdf
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: fa9f85cd9f4e97cc5655eeee
ciphertext: bab2fad2725ecde8486e17afb2ea44d908c023f80ee2592273e8ca7a2536
7c946d318f3bf241038f9ebd0267b3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: fa9f85cd9f4e97cc5655eeef
ciphertext: 63270c658fe7f960837760b763d487ba9b663643a3843399328aa90d06a1
9046e76b6e5a23460dec758b41a03c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: fa9f85cd9f4e97cc5655eeec
ciphertext: 9ee05381c12b4ac0d6fdddfb0efaf7ebe126474af24785af7ead4730b338
2155a7924996410f42905b05a7a3de

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: fa9f85cd9f4e97cc5655eeea
ciphertext: 971ba4154f709dcd45fd46b3a7cf53cfaa34ffcf8758c7bc6beea9e91b57
25cd611356da09dff633517c9284d2

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: fcdcc1cd73bf5cc87b991ca1f7b2f4f0ec2aac20e105efcb7111177a150af48c
seedR: 483bb0a0fe639035e3909be5c43af275da1cc8a0f355385fc4c7af211fbcad60
enc: 042eba2b8c1fa16ee99ab9f4627aee2358f71d6240955e5747ab869b5531a43ddab
8dec00e9fbdfb2f92073774a9981f72312ff6361b551bb254295fffea04de02
shared_secret:
23df0808be6ebbef5822349e5dae008d2c1e9f4020367097bde447ed5fcf383e
key_schedule_context: 005193809f9701d761ad3e980ec406cc14ea789817d821d0cb
139989260f37f4c6d3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: e0001a90ebb7efc5e85e1f72c90ea2e98b14c0431379789250bd2acda2a95208
key: 652abfcff470224fec73d73cef7c424401cb4d72d92ff5a8447a865c19830535
nonce: 07e632ae808cddf6acaeb15b
exporter_secret:
f3a31ef376affde7513fa5989ffadf6e32b8c7ee40a71d2c2f890dda77a5dadd
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 07e632ae808cddf6acaeb15b
ciphertext: edcfa837ec3e00787a52b462ac2a3a438a75e8df971fd21fa617998398c3
4ecfb69b4878faaa68c21edc39be2a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 07e632ae808cddf6acaeb15a
ciphertext: 02dfb0620b7d7835f66dd53b3444742649104532a808aab474b13c311b3d
5dfb99e80f00988b9e70546c369021

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 07e632ae808cddf6acaeb159
ciphertext: f42d3def0a450bbf6d15a6950a64c198bd36760a9b53e775bc3e60f9ec38
253597b725181e6d3b5feaa0ad80ef

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 07e632ae808cddf6acaeb15f
ciphertext: 03769cf4d9e13994376ee35afd627b9f7d1f495ae2d1d3538c4c803e9c08
aa13cf9ae7ec545c0f17b28d6b1cba

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: d5f77ccc5d8a284a97f6c9c72fa5cba1daff07cb177770796733129a39de0c14
seedR: 4ac36e24812130586b5326c046de98d3186124dedc8fa6afe6bb1181540bd0f7
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04f6ddb4c4f41ec4c1577e34519fb3a5b8d659945d425b4b117e02636841c4287fa
34bab4c35a5d41d788a8c321b8256cd71c93ff4a8799ed28301114196f9f6a6
shared_secret:
c6ab3fe04a92b975f5fd98a09db71063814b03ba86a69da3004e3a0dda8bbc40
key_schedule_context: 017d40471421306b100f7401fbf733fef208e1508bd2744517
e95ef7471f21a1dad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 6ab05d9bade32456ac456527e164651f1e7b90a22cec55cd32878dd4770271bc
key: abc5af188ea872c94cafd11dbdb7836cc1930ca0271833ba2a36a04d54404912
nonce: 4724facf9d0af1c7a55a0560
exporter_secret:
38e87692f83d991b20e731e1a29fa86bb92630824de1df6aeaf04fd4d59778e9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4724facf9d0af1c7a55a0560
ciphertext: 6972d38453567d2624db55ad748d42ff3177d1e941bbe57f68d03b53fb0f
1d48b6fc2dfcb84d8ef39f3a8ad6c5

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4724facf9d0af1c7a55a0561
ciphertext: 6ff2faf2ec58ddd27c3a97a25a1d1b3db45484f2bb1c84c751f58c03d660
cee4b942a10bac339044bd65157c65

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4724facf9d0af1c7a55a0562
ciphertext: e2203b51c7d776ed347168dd7d93066184bb7e775277dea7f95bcc3e897c
edd52fdcea492158116a8354387f85

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4724facf9d0af1c7a55a0564
ciphertext: c953c3657872749b048d8245ef98cf33a2f7e4c62f27d9b9e3496fdf50b9
51e63031092466f4bc67fb93bcee82

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 336770111a4f3e97ddd1592a15e4734b910b9a5b566e846cd8f28c6199f8c5e7
seedR: df66678a95aaf77b4a3ec2635b23b181dd3d8a05c68022cb6d5d71b119c1535d
seedS: 01bbe1ed07b0688a97d888880ca203b9ac5ebf298f4a5a081e1fa46dbb6e183f
enc: 044b364b95db5fadf0617c48688eed541aab99ddf72a5357ae371c34df7803fcd0d
a422f17ce4c68d03fef7c6ab272041230a3901361445644c2a6c3d02e9532c5
shared_secret:
f7b6fa8884784f6723692603cd958db6830cb0c87718f72cdff10758cb97a3ab
key_schedule_context: 025193809f9701d761ad3e980ec406cc14ea789817d821d0cb
139989260f37f4c6d3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 53be166abcfea99cf7bbe7c20e3704bccee414244cebed9dd5a2bc9f3ffe1600
key: 807c3ed1b3fdfa8ffb052e01e2f60e75aa9f47ed8378c17ad737e58f32954888
nonce: 7c84b0a76e3bff59f55eeb66
exporter_secret:
ad0c4d9ecace4d473c702f15f83c14964abc8340d560fb103a8ed9e96d30477a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7c84b0a76e3bff59f55eeb66
ciphertext: b626e15a016a4d1141404694d4f42300324839c26442761558aff3f11bea
d5af3102ca3eaa3d9ebe7d61b5e9ad

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7c84b0a76e3bff59f55eeb67
ciphertext: 9a71859d14fc01dd756e9c5ae3bd17f30276f60702913ed52d9bdd1f984d
d3c1f8d8da0e3cf80d7948322e5272

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7c84b0a76e3bff59f55eeb64
ciphertext: 56e9a11b272337128786b69cbf4969d92bfa91ff642c76815c3ed4169d87
08d1736466d5ba124de3de05e274ed

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7c84b0a76e3bff59f55eeb62
ciphertext: 47c2b0dd4cc2a0cdb9ece76eca03d71556f33554f52800adc208c1c954a5
0035d3a0c442ad07e5a4a0af2d3987

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 7454e819f88659590461a91dff451738df7789f5b4ced005211ed7b264be713f
seedR: 5f587a548f7cba21c98ac0dfdac619e962aba8526339c7ad98e804abd9fcbf19
seedS: 1093c27b5e2719ffade39714b76a8e994341b019de9522d89133b41a200f97da
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 042b8f991a7f0e1a833f58ce65bf65c96780e9620ae3ab6e8df1645b54b70ed89ad
bc9c2db9f4b6a0c7c08a76523f24ccbd555da8cdd0403e5f1aaf3f68e0dc62d
shared_secret:
ae88d508550ecc1804706bf7ef31c329cd2475f20b3ce3082207dc7c806121d5
key_schedule_context: 037d40471421306b100f7401fbf733fef208e1508bd2744517
e95ef7471f21a1dad3da0100c16489caa7ad5adf41151b806e7a2a438b79586881afdfaf
8bc6fedd
secret: 35a0d70ef7522b31c1d534e268a6d5139b0943b598e61c1c81f8d21633f459cf
key: 2fc299bf7d673aa547d3cb9972a7976bc262508c52a1a84c617e0f0b6bca3c39
nonce: 4af68b1b2cd29814fc8020d5
exporter_secret:
6370cd9058b498d3db6cce9beb618b094ff0981b846d5cf59676cd7e5e41dd3b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4af68b1b2cd29814fc8020d5
ciphertext: 694ad6fefd198fece3706b5fd6fb696ed03f399f3bdfabaec36b52fa6315
3db22a50978c6b0329a6c583a7380b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4af68b1b2cd29814fc8020d4
ciphertext: b0f4eeb0f9ef54c9f5dbc1b16dec408dc4160e255e768b00cc21aec6c5fb
65b29835131275ce081ff80e9f05ff

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4af68b1b2cd29814fc8020d7
ciphertext: 7d72a1eaeb27669fe6fa123a6c4bebecfe9fc035c8b0b2402ccab99dd92c
4047c9953a537fb1e647b9e8d49e0f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4af68b1b2cd29814fc8020d1
ciphertext: b55b04cb0cfa1911bf1c4cef46fdafeb2352de13cdb25e254d4b611ae59c
b2342208ccd645e4be0f6d02a34125

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 1ed3768f499b5b3c2beda3166528b649d4b117a0bd450f0e9e19815c2597d1777
ac67ea367415fb28c8819c94b383a0a8a15c9f03b4835330e3e6c8bc8319202e473
seedR: 62641514bccd2858f3d6513305288d6ca0e443f00a86eb33ccd519d1803aebc5d
07bbad0e1013ce61d9c9d713b3c90c8e79a1af01d6c69750f67cbbd1d9d4afeedfa
enc: 04000fe222a93e988f2b890bf98345fdd3c08724631091dfbd8c3572a91e2fc8bd8
78f1537852bffdaaf55e168cfa4511445c390a705bf322ded61f4bf7e5a9f69248101acb
73eb821bf6c757ab35286af062fa59f614e319c7eb62a1423c84c86eba1ae8d65280fd69
916ff758825e2944c2df3242b3f6b110da559bf20919431cab76cfa
shared_secret: 836dec8ee53432fe6135a364858d61a256848874d645c286d454411ee
fde448bc7654cf506bf1e4ab3dd43f5d9baeb05b24e2ee6b3591b5136432ff747c71722
key_schedule_context: 005c0b2bdbbffbea1af82c95fa5560defe4ba0a05fd3c301cd
fab3bbc2fba9783d13d14ecba2cdc7a7c1f544087eb5b3a22ca199e34879b2bbeab3d644
cb2a005dd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: 71529ceee3d8881f66363e99cd1bade88b2ea7b8c19363fc0e093bb92b961c31
d61e9147aeed52bc81be1e4f5ce18bb758a97dc54030e63ce37d3a92860328d6
key: 80358d48c8324176a44632f90c826a6bbfe7b2126f9ee47eca65f58faee8946f
nonce: 7502fc65d8e5db6fd14285c5
exporter_secret: d876060f03e1ba934c3e3c93416e91888b0a02614f8c5a27d24f311
2754c4d654bbc04fd54c1aa052c5dd81358362ecea1c15e20c9cebaa5393e52da73d4f61
1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7502fc65d8e5db6fd14285c5
ciphertext: ba38cbcd619868b4e993b7757cf8449aeab47d07741a62ec8b3fa72c136b
7e5f6c11ee2faceea367f4126181ca

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7502fc65d8e5db6fd14285c4
ciphertext: a97932db8c889e85e844b1b8fc75fb3a21e25569bcfacc74ce47287eb35b
59372f0e6c1762446674aec9469774

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7502fc65d8e5db6fd14285c7
ciphertext: dffe364d097f06751044647b5b992a834414c0d629b25f9db8e0bde6687e
26f73cd7f77078bd9d677a4e3555ed

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7502fc65d8e5db6fd14285c1
ciphertext: e48c2e05ec38338e78a2ed2473a6052006f474957d9ff98ff26c07d51418
bda9bebb572b6a46bdb8367a65595c

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 64463def238f309f1e9d1f28c15dc126cffa4ded911a4c527eeb71ba593847fb4
05756239d2c694ce4effa3996cafb5cc0b3736dd988deb7289210ec92bf6b339302
seedR: 41b782c18c14986c9d7a636152f13677aeddf479c1c7791ea46e0ebbe35ca9dd5
24c23d730eef443741d7d965415833d6c549c8c1b31ad05f2b9a88f916b2930528e
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 040041d3923b7218cf378f7336712e2ab1d254a2e7b0e67b85ccd149f68115e9d1e
d4492f5542923586feecf2e5500be432e181e73bbcf87947914ba760ab1216e62f80067e
0e0899fbc87ffcf0b2e7556f4bac9395aa3e284f73323c87ab3e5bb8409e2b85ed657170
aacad0d83cd8ea71dee1b480634f818383d75899c877d3fa263fe49
shared_secret: 8fb618ff94fca65c1bb2183b5683bbefd0aefe66d1610e0d1623c8b3d
00c2fb5feba21b1050d7752ad1f0b52250624881902f3d5156b4b3c454aaee2b2b20a89
key_schedule_context: 017344e204124da2a856fc5693999bbfd1242c27f4b2f16fdc
92751d458fbb606adde7aecc32db4dd5b0fdbea7655c7c0e8363da1a34370ba59bfdb421
08a4bebbd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: edfc1907ed7d5006b7e821f9802b49192ebd40dad26bb9ebc20192bfc4e6319f
22dd9950d51fe7c07c48739ff424509b056acf2a2acb655b59999626b91741b8
key: 6fb2ffb368d1d76a743b9e51d8293d0960810936399fb51dcffe83ddf14c6271
nonce: ba6d3b6c7435583230a60d86
exporter_secret: 1926473db83cdccbfc308c0a286b0e248c2d2cda275c6c511f50d64
768d483229f24f770271cdb01096bdcb15c8269ef5e80e592998fb43c93ea3b8c0e1e46d
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ba6d3b6c7435583230a60d86
ciphertext: 264cd2ede05a9ab1527a01508fd537afe67b6c6f89d5a09e9e28bb3e0a52
c61a174f9ae71681f548ec44b38ccd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ba6d3b6c7435583230a60d87
ciphertext: 4b439bc9afa3ce832cbda50c31b549fcab63a7ffd040907e1fdc5200e01d
5d0ba4b4349eda9c135d4b1a39da7d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ba6d3b6c7435583230a60d84
ciphertext: b8bf1321fa9d670cd0fea9c59ca8a88583f793a27633a8ab5b026e3309b7
861d98c1546ee4205621da2d5899c0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ba6d3b6c7435583230a60d82
ciphertext: 84a1574168983ccb5b52a5e0b522f04cf5283bd6e818e0f4c3b165e179ad
899e34f8675aea5b905605f10cfb15

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: 81dc51e31ef8e9b33fefcdf00bd3b0ff585b941fe76cf39a86c269e2f53be7edb
3db0be1a58b6cb8d8e6020fe8a2018c59d47cacb35b2b8c61bd4155438b5eda5c0d
seedR: 54af23ea93c8fc34deb6a7cd70e657ea8990fc4e9a18656d5764b62f7a33a9e02
12adeae1585ad2ef28688c1b558866c1975973c4dff08955c1f9fd7939b10b5fbfc
seedS: b65599d814192278ab826ef197a61b77db50f40495f77502dfaa03acd1f3565a3
cefebd59de2328ece0638c90d8a89f9ca58f2850e39e9a4c9c339290d66da12fdf0
enc: 0400c708757d53d8a1ac555426d660014fefab2676fcebf62d7589339f24a0f632e
51da9e1b13631f461a48753b756c3322032cc27b32cea63cfefadba56952d7ae35c0166b
63cc1e329938a33728a2ef6fce3372589da2b9bcc80ae007dee3e084b1656349f1514590
5689ef920807ff239f94891b22057385c7b97ea517b1ab21bf5fec8
shared_secret: 7258e75f7c2a8ded295523a7b99c1045925dca1628a91bdca9a2e1bdc
c187eee3b627f2ab6a73853c8dcb13a95d0980585c21c25cf92b7c9d945430dfc47e690
key_schedule_context: 025c0b2bdbbffbea1af82c95fa5560defe4ba0a05fd3c301cd
fab3bbc2fba9783d13d14ecba2cdc7a7c1f544087eb5b3a22ca199e34879b2bbeab3d644
cb2a005dd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: dc6a1631b3fbc9d6b6b856d60738cefe1743cfc14d1ae0627b38386b9abc9b2f
86dde080bb6b9d7c3eb579d6bf599765cb4a5e27cd134703acc06142901164c9
key: eedfdbacc250f004a9a4027184a95388f9ebf86ce9593c81921da9eef5d9f6e9
nonce: 8c1fb99aa9cca28b2a1ac3ec
exporter_secret: 1f64d525bc6f36488c46c0650b6f0c10a887e0e300737a2c167e4ff
d1b4d91193750fcf26173f0c8924f6a86b01fac3f6753d4e9f91abd92b042ae3218d7f45
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8c1fb99aa9cca28b2a1ac3ec
ciphertext: 1f4da6829a7336ec414ffeebec31807dd1acb2ec248b165b5d29732dd005
7fa76be483b9af01437b32ebe6c061

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8c1fb99aa9cca28b2a1ac3ed
ciphertext: 168714b29e7f1c3a91dffdb6cc576b7be34ef929b7ccd598435c4ef1af52
c5d7ddbe43f51ac50b27bbf9ce0e73

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8c1fb99aa9cca28b2a1ac3ee
ciphertext: 639d9f6c9ca75d91fff8d4a9b0608d10db800fe6a1ed208a09fb907f70a3
27c61414a20e4910a54f12f2ada7a6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8c1fb99aa9cca28b2a1ac3e8
ciphertext: e325abd75e86991abc1ba269fef64c5ccb3a5c1636f4c8e026205ad45470
cae1771d9a5c87a3a21af1d6b89cc0

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
seedE: dc1fda9b21a1af6925ecf9ad79d2422f698b4168587c7908b36f5f58352181b95
06554d8d8c9427e0dd2cfda25f0eabf58e9f5597e1b76ac12c799fe96e3cc03dc59
seedR: 46592c2b171b8cdcce89601fab103f63ed43badadcf9df62a928ae3b7fa91f269
eff3485f6401c374e19a8bb988005626b9c26d39795282b1095bcc4f62a67255e15
seedS: d02446c344c10cd162486caa69aa1156ac3066e0fd668fa7faaf13bdbc944edbc
0cd68ee36e4c30ecc36c2c5ab0978473eb1b5dcfff27985c9328877e85fd48b657d
psk: 5db3b80a81cb63ca59470c83414ef70a
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04007abb917b25112c8bf9a75233c90e0f55a4b6cd4f52a9f8a8856e85f82bbd84a
c0d1941f01aab2c7846e6b562c0f5168727f4443acb84249f357d591f7bef8651d2019e0
f9ef53c20a74f6cc9e6080e792877201ec7d4fb5fa22e184d1d848314811a3d110112172
bc802805ef7405dc0fac4f5f401865f0410c05d172524a71039963e
shared_secret: 82913b51b3809a9177ab90ca628e661126d8b64ca95739f6172b93ff5
11ccc0b7b6255dd9bc17d692b598acd10c1a3b86fb242554824f06df693f75c5d2935d6
key_schedule_context: 037344e204124da2a856fc5693999bbfd1242c27f4b2f16fdc
92751d458fbb606adde7aecc32db4dd5b0fdbea7655c7c0e8363da1a34370ba59bfdb421
08a4bebbd8854451600d718851b126f132b5ea0cf6942b64e7e586a7f8877bbcc281c8f6
c005e9d1c201fa65882d2162ed577741da4aed5c33fa050d83feb94a4e88638c
secret: fd3c39728bad99fcb7c2430841690994f624a2bcfaba38affe3596b651bae01c
cd0b7b1c9fbf10de0fddb9ec06bfc9dfcd0c1fcdb2cbfee6e27e4a653bc24344
key: 7262c38cfa0c8f468160fb1530579d53c433559a58bc1acf1facf5231bdbc7cf
nonce: 65560e6c300fd5a0a7dba420
exporter_secret: 58a7173f251e03619d615542539e40c9bf480f96efd026216211062
96dbff95aff003971cafb9265d92ba3d7fbf67283c40364f7def04cd4d6429c015172e76
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 65560e6c300fd5a0a7dba420
ciphertext: e0d4d9b38eb8b8dc1f2c986005a83b7df5bde76d48c95dd59bd60456639a
82feb3ea3205b6fce5e672fad9c73d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 65560e6c300fd5a0a7dba421
ciphertext: a905aa5e9c23600c8bdd8c45b2bdd3352727175c565d4d60b7e4d7083b10
fe26afde4ccdab36726e6e0c26d78f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 65560e6c300fd5a0a7dba422
ciphertext: f8d5733f3b2e850176ae68f998268125662161b4edf86752a80b70ec0376
2dcbb8508c495852fc313cbca8e065

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 65560e6c300fd5a0a7dba424
ciphertext: 644ce2fe731274c00b455a25e7a733032dd2916d25a4a39d28a89f3f5282
b12b20afde48860ea31f187c4c4ecd

~~~
