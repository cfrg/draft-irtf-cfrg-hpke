# Hybrid Public Key Encryption

This is the working area for the individual Internet-Draft, "Hybrid Public Key Encryption".

* [Editor's Copy](https://cfrg.github.io/draft-irtf-cfrg-hpke/#go.draft-irtf-cfrg-hpke.html)
* [Individual Draft](https://tools.ietf.org/html/draft-irtf-cfrg-hpke)
* [Compare Editor's Copy to Individual Draft](https://cfrg.github.io/draft-irtf-cfrg-hpke/#go.draft-irtf-cfrg-hpke.diff)

## Building the Draft

Formatted text and HTML versions of the draft can be built using `make`.

```sh
$ make
```

This requires that you have the necessary software installed.  See
[the instructions](https://github.com/martinthomson/i-d-template/blob/master/doc/SETUP.md).

# Existing HPKE implementations

| Implementation                                     | Language | Version  | Modes  |
| -------------------------------------------------- |:---------|:---------|:-------|
| [go-hpke](https://github.com/cisco/go-hpke)        | Go       | draft-08 | All    |
| [CIRCL](https://github.com/cloudflare/circl/tree/master/hpke) | Go       | draft-08 | All but "Export Only" |
| [hpke-compact](https://github.com/jedisct1/go-hpke-compact)   | Go       | draft-08 | All    |
| [rust-hpke](https://github.com/rozbb/rust-hpke)    | Rust     | draft-08 | All    |
| [BoringSSL](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/include/openssl/hpke.h) | C | draft-08 | Base |
| [NSS](https://hg.mozilla.org/projects/nss/file/tip/lib/pk11wrap) | C | draft-08 | Base, PSK |
| [hpke-rs](https://github.com/franziskuskiefer/hpke-rs)    | Rust     | draft-08 | All    |
| [happykey](https://github.com/sftcd/happykey) | C/OpenSSL | draft-08 | All |
| [hpke-wrap](https://github.com/danharkins/hpke-wrap) | C/OpenSSL | draft-08 | All |
| [zig-hpke](https://github.com/jedisct1/zig-hpke) | Zig | draft-08 | All |
| [libhpke](https://github.com/cisco/mlspp/tree/main/lib/hpke) | C++ (OpenSSL) | draft-08 | All |
| [hacl-star-hpke](https://github.com/project-everest/hacl-star/blob/_blipp_hpke/specs/Spec.Agile.HPKE.fsti) | F\* | draft-05 | All |
| [hpke-js](https://github.com/dajiaji/hpke-js) | TypeScript | RFC9180 | All |

Submit a PR if you would like your implementation to be added!

## Contributing

See the
[guidelines for contributions](https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/master/CONTRIBUTING.md).
