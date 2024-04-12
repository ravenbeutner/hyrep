# Benchmarks

This `benchmarks/` folder contains the benchmarks used to evaluate HyRep in [1].
We provide the command-line instructions to run all instances (when run from the main diretcory ). 

## Iterative Repair

```
./app/HyRep --iter benchmarks/iterative/1_edas/edas.txt
./app/HyRep --iter benchmarks/iterative/2_csrf/csrf.txt
./app/HyRep --iter benchmarks/iterative/3_bank/bank1.txt
./app/HyRep --iter benchmarks/iterative/3_bank/bank2.txt
./app/HyRep --iter benchmarks/iterative/3_bank/bank3.txt
./app/HyRep --iter benchmarks/iterative/4_reviews/2reviewsV1.txt
./app/HyRep --iter benchmarks/iterative/4_reviews/2reviewsV2.txt
./app/HyRep --iter benchmarks/iterative/4_reviews/3reviewsV1.txt
./app/HyRep --iter benchmarks/iterative/5_atm/atmV1.txt
./app/HyRep --iter benchmarks/iterative/5_atm/atmV2.txt
```

## Scalability in Solution Size

```
./app/HyRep --iter benchmarks/scale/scale_1.txt
./app/HyRep --iter benchmarks/scale/scale_2.txt
./app/HyRep --iter benchmarks/scale/scale_3.txt
./app/HyRep --iter benchmarks/scale/scale_4.txt
./app/HyRep --iter benchmarks/scale/scale_5.txt
./app/HyRep --iter benchmarks/scale/scale_6.txt
./app/HyRep --iter benchmarks/scale/scale_7.txt
```


## k-Safety Instances 

```
./app/HyRep --repair benchmarks/k-safety/coll_item_sym.txt
./app/HyRep --repair benchmarks/k-safety/counter_det.txt
./app/HyRep --repair benchmarks/k-safety/double_square_ni_ff.txt
./app/HyRep --repair benchmarks/k-safety/double_square_ni.txt
./app/HyRep --repair benchmarks/k-safety/exp1x3.txt
./app/HyRep --repair benchmarks/k-safety/fig2.txt
./app/HyRep --repair benchmarks/k-safety/fig3.txt
./app/HyRep --repair benchmarks/k-safety/mult_equiv.txt
```

## Functional Properties 

```
./app/HyRep --repair benchmarks/functional/assignment.txt
./app/HyRep --repair benchmarks/functional/deletion.txt
./app/HyRep --repair benchmarks/functional/guard.txt
./app/HyRep --repair benchmarks/functional/long-output.txt
./app/HyRep --repair benchmarks/functional/multiline.txt
./app/HyRep --repair benchmarks/functional/not-equal.txt
./app/HyRep --repair benchmarks/functional/simple-example.txt
./app/HyRep --repair benchmarks/functional/off-by-one.txt
```


## References

[1] Beutner, Hsu, Bonakdarpour, Finkbeiner. Syntax-Guided Automated Program Repair for Hyperproperties. CAV 2024
