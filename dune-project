(lang dune 3.16)

(using menhir 2.0)

(name silver)

(generate_opam_files true)

(source
 (github csmith49/silver))

(authors "Calvin Smith")

(license MIT)

(package
 (name silver)
 (synopsis "Proof techniques for probabilistic Hoare triples")
 (depends
  (ocaml
   (>= 5.2.0))
  (dune
   (>= 3.16))
  menhir
  (zarith
   (>= 1.14))
  (z3
   (>= 4.13.0))
  (containers
   (>= 3.14))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
