// src/main.rs

mod functional_quicksort;

// Standard imperative quicksort implementation (for comparison)
fn quicksort<T: Ord + Clone>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    
    // Sort the left part
    quicksort(&mut arr[0..pivot_index]);
    // Sort the right part
    quicksort(&mut arr[pivot_index + 1..len]);
}

fn partition<T: Ord + Clone>(arr: &mut [T]) -> usize {
    let len = arr.len();
    
    // Use last element as pivot
    let pivot_index = len - 1;
    let pivot = arr[pivot_index].clone();
    
    // Index of smaller element
    let mut i = 0;
    
    // Move all elements smaller than pivot to the left side
    for j in 0..len - 1 {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    // Move pivot to its final position
    arr.swap(i, pivot_index);
    
    i // Return the pivot's final position
}

fn basic_quicksort_demo() {
    // Example usage with integers
    let mut numbers = vec![10, 7, 8, 9, 1, 5];
    println!("Unsorted array: {:?}", numbers);
    
    quicksort(&mut numbers);
    
    println!("Sorted array: {:?}", numbers);
    
    // Example usage with strings
    let mut words = vec!["banana", "apple", "cherry", "date", "elderberry"];
    println!("Unsorted words: {:?}", words);
    
    quicksort(&mut words);
    
    println!("Sorted words: {:?}", words);
}

fn functional_quicksort_demo() {
    use functional_quicksort::*;
    
    println!("\n--- Functional Quicksort Demo ---");
    
    // Example with integers
    let numbers = vec![10, 7, 8, 9, 1, 5];
    println!("Original numbers: {:?}", numbers);
    
    let sorted_numbers = quicksort_functional_ord(&numbers);
    println!("Sorted numbers: {:?}", sorted_numbers);
    println!("Original numbers (unchanged): {:?}", numbers);
    
    // Example with custom comparison function (sort in descending order)
    let sorted_desc = quicksort_functional(&numbers, |a, b| b.cmp(a));
    println!("Sorted in descending order: {:?}", sorted_desc);
    
    // Example with transformation
    println!("\nTransformation example:");
    let people = vec![
        ("Alice", 29),
        ("Bob", 31),
        ("Charlie", 27),
        ("Diana", 31),
        ("Eva", 25),
    ];
    
    // Transform to select age and sort by it
    let sorted_ages = transform_and_sort(
        &people,
        |p| p.1,          // transform: extract age
        |a, b| a.cmp(b)   // compare: default ordering
    );
    
    println!("Ages sorted: {:?}", sorted_ages);
    
    // Transform to select name and sort by it
    let sorted_names = transform_and_sort(
        &people,
        |p| p.0.to_string(),  // transform: extract name
        |a, b| a.cmp(b)       // compare: default ordering
    );
    
    println!("Names sorted: {:?}", sorted_names);
    
    // Word frequency analysis demo
    println!("\nWord frequency analysis:");
    let text = "Rust is a multi-paradigm programming language focused on performance and safety, \
                especially safe concurrency. Rust is syntactically similar to C++, but provides \
                memory safety without using garbage collection. Rust was originally designed by \
                Graydon Hoare at Mozilla Research, with contributions from Dave Herman, Brendan Eich, \
                and others. The designers refined the language while writing the Servo layout or \
                browser engine, and the Rust compiler. The compiler is free and open-source software \
                dual-licensed under the MIT License and Apache License 2.0.";
    
    let word_frequencies = word_frequency_analysis(text);
    
    println!("Top 10 most frequent words:");
    for (i, (word, count)) in word_frequencies.iter().take(10).enumerate() {
        println!("{}. {} - {} occurrences", i + 1, word, count);
    }
}

fn main() {
    // Run the basic quicksort demo
    basic_quicksort_demo();
    
    // Run the functional quicksort demo
    functional_quicksort_demo();
}
