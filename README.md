# SIFT
SIFT: Symbolic Execution with Selective Thread Scheduling

SIFT is built on top of PROMPT and the KLEE Symbolic Virtual Machine to implement a multi-threaded 
symbolic executor. SIFT deals with the path explosion problem due to thread interleavings 
through a selective scheduling approach. It performs an on-the-fly dependency analysis based 
on the explored symbolic execution paths to identify property relevant interleaving points at 
which context switches are performed. SIFT supports both assertion checks and memory safety 
properties.

If you use SIFT, please cite the following paper:

@inproceedings{Yavuz22,
  author =       {Tuba Yavuz},
  title =        {{SIFT: A Tool for Property Directed Symbolic Execution of Multithreaded Software}}
  booktitle =    {{2022 IEEE Conference on Software Testing, Verification and Validation (ICST)}}
  year =         {2022},
}
