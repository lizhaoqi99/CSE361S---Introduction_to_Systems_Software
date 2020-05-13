I wrote a general-purpose struct-based dynamic storage allocator for C programs; i.e., my own
version of the malloc, free, and realloc routines. In specific, I implemented 
using eleven segregated lists that each corresponds to a specific block size range, 
and I removed the footer of each block.
