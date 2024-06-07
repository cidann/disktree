use std::collections::BTreeMap;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use disktree::{tree::{self, StubPageTable, Tree}, utils::{generate_indexex, generate_string}};
use proptest::collection::BTreeMapStrategy;




fn compare_node_std_btree(c:&mut Criterion){


    let mut group=c.benchmark_group("insert_get");
    group.bench_function(
        BenchmarkId::new("disktree", 1000),
        |i|{
            i.iter_batched_ref(
                ||{
                    let stub_table=StubPageTable::new();
                    (
                        stub_table,
                        (0..1000).map(|_|(generate_string(10..200),generate_string(10..200))).collect::<Vec<_>>(),
                        generate_indexex(0..1000)
                    )
                },
                |(table,kv,idx)|{
                    let mut tree:Tree<StubPageTable, tree::Lexicological>=Tree::new(tree::PAGE_SIZE,table);
                    for (k,v) in kv.iter(){
                        tree.insert(k.as_bytes(), v.as_bytes());
                    }
                    for i in idx.iter(){
                        tree.get(kv[*i].0.as_bytes());
                    }
                },
                criterion::BatchSize::PerIteration
            )
        }
    );

    group.bench_function(
        BenchmarkId::new("btree", 1000),
        |i|{
            i.iter_batched_ref(
                ||{
                    (
                        (0..1000).map(|_|(generate_string(10..200),generate_string(10..200))).collect::<Vec<_>>(),
                        generate_indexex(0..1000)
                    )
                },
                |(kv,idx)|{
                    let mut tree=BTreeMap::new();
                    
                    for (k,v) in kv.iter(){
                        tree.insert(k.clone(), v.clone());
                    }
                    for i in idx.iter(){
                        tree.get(&kv[*i].0);
                    }
                },
                criterion::BatchSize::PerIteration
            )
        }
    );
}

criterion_group!(compare_std,compare_node_std_btree);
criterion_main!(compare_std);