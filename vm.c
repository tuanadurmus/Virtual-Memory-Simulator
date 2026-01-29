#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vm_dbg.h"

#define NOPS (16)

#define OPC(i) ((i) >> 12)
#define DR(i) (((i) >> 9) & 0x7)
#define SR1(i) (((i) >> 6) & 0x7)
#define SR2(i) ((i) & 0x7)
#define FIMM(i) ((i >> 5) & 01)
#define IMM(i) ((i) & 0x1F)
#define SEXTIMM(i) sext(IMM(i), 5)
#define FCND(i) (((i) >> 9) & 0x7)
#define POFF(i) sext((i) & 0x3F, 6)
#define POFF9(i) sext((i) & 0x1FF, 9)
#define POFF11(i) sext((i) & 0x7FF, 11)
#define FL(i) (((i) >> 11) & 1)
#define BR(i) (((i) >> 6) & 0x7)
#define TRP(i) ((i) & 0xFF)

/* New OS declarations */

// OS bookkeeping constants
#define PAGE_SIZE       (2048)  // Page size in words (of 2 bytes)
#define OS_MEM_SIZE     (2)     // OS Region size. Also the start of the page tables' page
#define Cur_Proc_ID     (0)     // id of the current process
#define Proc_Count      (1)     // total number of processes, including ones that finished executing.
#define OS_STATUS       (2)     // Bit 0 shows whether the PCB list is full or not
#define OS_FREE_BITMAP  (3)     // Bitmap for free pages

// Process list and PCB related constants
#define PCB_SIZE  (3)  // Number of fields in a PCB
#define PID_PCB   (0)  // Holds the pid for a process
#define PC_PCB    (1)  // Value of the program counter for the process
#define PTBR_PCB  (2)  // Page table base register for the process

#define CODE_SIZE       (2)  // Number of pages for the code segment
#define HEAP_INIT_SIZE  (2)  // Number of pages for the heap segment initially

bool running = true;

typedef void (*op_ex_f)(uint16_t i);
typedef void (*trp_ex_f)();

enum { trp_offset = 0x20 };
enum regist { R0 = 0, R1, R2, R3, R4, R5, R6, R7, RPC, RCND, PTBR, RCNT };
enum flags { FP = 1 << 0, FZ = 1 << 1, FN = 1 << 2 };

uint16_t mem[UINT16_MAX + 1] = {0};
uint16_t reg[RCNT] = {0};
uint16_t PC_START = 0x3000;

void initOS();
int createProc(char *fname, char *hname);
void loadProc(uint16_t pid);
uint16_t allocMem(uint16_t ptbr, uint16_t vpn, uint16_t read, uint16_t write);  // Can use 'bool' instead
int freeMem(uint16_t ptr, uint16_t ptbr);
static inline uint16_t mr(uint16_t address);
static inline void mw(uint16_t address, uint16_t val);
static inline void tbrk();
static inline void thalt();
static inline void tyld();
static inline void trap(uint16_t i);

static inline uint16_t sext(uint16_t n, int b) { return ((n >> (b - 1)) & 1) ? (n | (0xFFFF << b)) : n; }
static inline void uf(enum regist r) {
    if (reg[r] == 0)
        reg[RCND] = FZ;
    else if (reg[r] >> 15)
        reg[RCND] = FN;
    else
        reg[RCND] = FP;
}
static inline void add(uint16_t i)  { reg[DR(i)] = reg[SR1(i)] + (FIMM(i) ? SEXTIMM(i) : reg[SR2(i)]); uf(DR(i)); }
static inline void and(uint16_t i)  { reg[DR(i)] = reg[SR1(i)] & (FIMM(i) ? SEXTIMM(i) : reg[SR2(i)]); uf(DR(i)); }
static inline void ldi(uint16_t i)  { reg[DR(i)] = mr(mr(reg[RPC]+POFF9(i))); uf(DR(i)); }
static inline void not(uint16_t i)  { reg[DR(i)]=~reg[SR1(i)]; uf(DR(i)); }
static inline void br(uint16_t i)   { if (reg[RCND] & FCND(i)) { reg[RPC] += POFF9(i); } }
static inline void jsr(uint16_t i)  { reg[R7] = reg[RPC]; reg[RPC] = (FL(i)) ? reg[RPC] + POFF11(i) : reg[BR(i)]; }
static inline void jmp(uint16_t i)  { reg[RPC] = reg[BR(i)]; }
static inline void ld(uint16_t i)   { reg[DR(i)] = mr(reg[RPC] + POFF9(i)); uf(DR(i)); }
static inline void ldr(uint16_t i)  { reg[DR(i)] = mr(reg[SR1(i)] + POFF(i)); uf(DR(i)); }
static inline void lea(uint16_t i)  { reg[DR(i)] =reg[RPC] + POFF9(i); uf(DR(i)); }
static inline void st(uint16_t i)   { mw(reg[RPC] + POFF9(i), reg[DR(i)]); }
static inline void sti(uint16_t i)  { mw(mr(reg[RPC] + POFF9(i)), reg[DR(i)]); }
static inline void str(uint16_t i)  { mw(reg[SR1(i)] + POFF(i), reg[DR(i)]); }
static inline void rti(uint16_t i)  {} // unused
static inline void res(uint16_t i)  {} // unused
static inline void tgetc()        { reg[R0] = getchar(); }
static inline void tout()         { fprintf(stdout, "%c", (char)reg[R0]); }
static inline void tputs() {
  uint16_t *p = mem + reg[R0];
  while(*p) {
    fprintf(stdout, "%c", (char) *p);
    p++;
  }
}
static inline void tin()      { reg[R0] = getchar(); fprintf(stdout, "%c", reg[R0]); }
static inline void tputsp()   { /* Not Implemented */ }
static inline void tinu16()   { fscanf(stdin, "%hu", &reg[R0]); }
static inline void toutu16()  { fprintf(stdout, "%hu\n", reg[R0]); }

trp_ex_f trp_ex[10] = {tgetc, tout, tputs, tin, tputsp, thalt, tinu16, toutu16, tyld, tbrk};
static inline void trap(uint16_t i) { trp_ex[TRP(i) - trp_offset](); }
op_ex_f op_ex[NOPS] = {/*0*/ br, add, ld, st, jsr, and, ldr, str, rti, not, ldi, sti, jmp, res, lea, trap};

/**
  * Load an image file into memory.
  * @param fname the name of the file to load
  * @param offsets the offsets into memory to load the file
  * @param size the size of the file to load
*/
void ld_img(char *fname, uint16_t *offsets, uint16_t size) {
    FILE *in = fopen(fname, "rb");
    if (NULL == in) {
        fprintf(stderr, "Cannot open file %s.\n", fname);
        exit(1);
    }

    for (uint16_t s = 0; s < size; s += PAGE_SIZE) {
        uint16_t *p = mem + offsets[s / PAGE_SIZE];
        uint16_t writeSize = (size - s) > PAGE_SIZE ? PAGE_SIZE : (size - s);
        fread(p, sizeof(uint16_t), (writeSize), in);
    }
    
    fclose(in);
}

void run(char *code, char *heap) {
  while (running) {
    uint16_t i = mr(reg[RPC]++);
    op_ex[OPC(i)](i);
  }
}

// YOUR CODE STARTS HERE



#define PCB_START_ADDR  (12)
#define PT_START_ADDR   (OS_MEM_SIZE * PAGE_SIZE)           
#define PT_ENTRIES      (32)                             
#define PT_LIMIT_ADDR   (PT_START_ADDR + PAGE_SIZE)         
#define OS_LIMIT_ADDR   (OS_MEM_SIZE * PAGE_SIZE)           

static inline uint16_t pcb_addr(uint16_t pid) {
  return (uint16_t)(PCB_START_ADDR + pid * PCB_SIZE);
}

static inline uint16_t ptbr_for_pid(uint16_t pid) {
  return (uint16_t)(PT_START_ADDR + pid * PT_ENTRIES);
}


#define CODE_VPN0 ((uint16_t)(PC_START >> 11))       
#define CODE_VPN1 ((uint16_t)(CODE_VPN0 + 1))       
#define HEAP_VPN0 ((uint16_t)(CODE_VPN1 + 1))      
#define HEAP_VPN1 ((uint16_t)(HEAP_VPN0 + 1))       



static inline uint16_t bitmap_word_index(uint16_t pfn) {
  return (uint16_t)(OS_FREE_BITMAP + (pfn / 16));
}

static inline uint16_t bitmap_bit_index(uint16_t pfn) {
  return (uint16_t)(15 - (pfn % 16));
}

static inline bool bitmap_is_free(uint16_t pfn) {
  uint16_t idx = bitmap_word_index(pfn);
  uint16_t bit = bitmap_bit_index(pfn);
  return (mem[idx] >> bit) & 1u;     
}

static inline void bitmap_mark_used(uint16_t pfn) {
  uint16_t idx = bitmap_word_index(pfn);
  uint16_t bit = bitmap_bit_index(pfn);
  mem[idx] &= (uint16_t)~(1u << bit); 
}

static inline void bitmap_mark_free(uint16_t pfn) {
  uint16_t idx = bitmap_word_index(pfn);
  uint16_t bit = bitmap_bit_index(pfn);
  mem[idx] |= (uint16_t)(1u << bit);  
}


static inline uint16_t* pte_ptr(uint16_t ptbr, uint16_t vpn) {
  return &mem[ptbr + vpn];
}

static inline bool pte_is_valid(uint16_t pte) {
  return (pte & 0x0001) != 0;        
}

static inline uint16_t pte_get_pfn(uint16_t pte) {
  return (uint16_t)(pte >> 11);     
}

static inline uint16_t make_pte(uint16_t pfn, bool r, bool w) {
  return (uint16_t)((pfn << 11) | ((w ? 1u : 0u) << 2) | ((r ? 1u : 0u) << 1) | 1u);
}
static inline uint16_t find_next_runnable_excluding_self(uint16_t cur_pid) {
  uint16_t n = mem[Proc_Count];
  if (n <= 1) return UINT16_MAX;

 
  for (uint16_t k = 1; k < n; k++) {
    uint16_t cand = (uint16_t)((cur_pid + k) % n);
    uint16_t pcb = pcb_addr(cand);
    if (mem[pcb + PID_PCB] != UINT16_MAX) { 
      return cand;
    }
  }
  return UINT16_MAX;
}


void initOS() {
  mem[Cur_Proc_ID] = 0xFFFF;
  mem[Proc_Count]  = 0x0000;
  mem[OS_STATUS]   = 0x0000;
  mem[OS_FREE_BITMAP]     = 0xFFFF;
  mem[OS_FREE_BITMAP + 1] = 0xFFFF; 

 
  for (uint16_t pfn = 0; pfn <= 2; pfn++) {
    uint16_t idx = OS_FREE_BITMAP + (pfn / 16);  
    uint16_t bit = 15 - (pfn % 16);
    mem[idx] &= (uint16_t)~(1u << bit);        
  }
}


int createProc(char *fname, char *hname) {
  if (mem[OS_STATUS] & 0x0001) {
    fprintf(stdout, "The OS memory region is full. Cannot create a new PCB.\n");
    return 0;
  }

  uint16_t pid = mem[Proc_Count];       
  uint16_t pcb = pcb_addr(pid);
  uint16_t ptbr = ptbr_for_pid(pid);


  if ((uint32_t)pcb + (PCB_SIZE - 1) >= OS_LIMIT_ADDR) {
    mem[OS_STATUS] |= 0x0001;
    fprintf(stdout, "The OS memory region is full. Cannot create a new PCB.\n");
    return 0;
  }


  if ((uint32_t)ptbr + (PT_ENTRIES - 1) >= PT_LIMIT_ADDR) {
    mem[OS_STATUS] |= 0x0001;
    fprintf(stdout, "The OS memory region is full. Cannot create a new PCB.\n");
    return 0;
  }


  for (uint16_t i = 0; i < PT_ENTRIES; i++) mem[ptbr + i] = 0;


  mem[pcb + PID_PCB]  = pid;
  mem[pcb + PC_PCB]   = PC_START;   
  mem[pcb + PTBR_PCB] = ptbr;


  mem[Proc_Count] = (uint16_t)(mem[Proc_Count] + 1);


  uint16_t code_offsets[2] = {0, 0};

  code_offsets[0] = allocMem(ptbr, CODE_VPN0, UINT16_MAX, 0);
  if (code_offsets[0] == 0) {
    fprintf(stdout, "Cannot create code segment.\n");
    return 0;
  }

  code_offsets[1] = allocMem(ptbr, CODE_VPN1, UINT16_MAX, 0);
  if (code_offsets[1] == 0) {

    freeMem(CODE_VPN0, ptbr);
    fprintf(stdout, "Cannot create code segment.\n");
    return 0;
  }


  ld_img(fname, code_offsets, (uint16_t)(CODE_SIZE * PAGE_SIZE));


  uint16_t heap_offsets[2] = {0, 0};

  heap_offsets[0] = allocMem(ptbr, HEAP_VPN0, UINT16_MAX, UINT16_MAX);
  if (heap_offsets[0] == 0) {

    freeMem(CODE_VPN0, ptbr);
    freeMem(CODE_VPN1, ptbr);
    fprintf(stdout, "Cannot create heap segment.\n");
    return 0;
  }

  heap_offsets[1] = allocMem(ptbr, HEAP_VPN1, UINT16_MAX, UINT16_MAX);
  if (heap_offsets[1] == 0) {

    freeMem(HEAP_VPN0, ptbr);
    freeMem(CODE_VPN0, ptbr);
    freeMem(CODE_VPN1, ptbr);
    fprintf(stdout, "Cannot create heap segment.\n");
    return 0;
  }


  ld_img(hname, heap_offsets, (uint16_t)(HEAP_INIT_SIZE * PAGE_SIZE));

  return 1;
}


void loadProc(uint16_t pid) {
  uint16_t pcb = pcb_addr(pid);
  reg[RPC]  = mem[pcb + PC_PCB];
  reg[PTBR] = mem[pcb + PTBR_PCB];
  mem[Cur_Proc_ID] = pid;
}


uint16_t allocMem(uint16_t ptbr, uint16_t vpn, uint16_t read, uint16_t write) {

  uint16_t *pte_addr = pte_ptr(ptbr, vpn);
  uint16_t old = *pte_addr;

  if (pte_is_valid(old)) return 0;

  int found = -1;
  for (uint16_t pfn = 0; pfn < 32; pfn++) {
    if (bitmap_is_free(pfn)) { found = (int)pfn; break; }
  }
  if (found < 0) return 0; 

  uint16_t pfn = (uint16_t)found;

  bitmap_mark_used(pfn);

  bool r = (read == UINT16_MAX);
  bool w = (write == UINT16_MAX);

  *pte_addr = make_pte(pfn, r, w);

  return (uint16_t)(pfn * PAGE_SIZE);
}

int freeMem(uint16_t vpn, uint16_t ptbr) {

  uint16_t *pte_addr = pte_ptr(ptbr, vpn);
  uint16_t pte = *pte_addr;

  if (!pte_is_valid(pte)) return 0;

  uint16_t pfn = pte_get_pfn(pte);


  bitmap_mark_free(pfn);


  *pte_addr = (uint16_t)(pte & (uint16_t)~1u);

  return 1;
}

static inline void tbrk() {
  uint16_t cur = mem[Cur_Proc_ID];

  uint16_t r0  = reg[R0];
  uint16_t vpn = (uint16_t)(r0 >> 11);     
  uint16_t w   = (uint16_t)((r0 >> 2) & 1);  
  uint16_t r   = (uint16_t)((r0 >> 1) & 1); 
  uint16_t a   = (uint16_t)(r0 & 1);       


  uint16_t code_vpn0 = (uint16_t)(PC_START >> 11); 
  if (vpn < code_vpn0) {
    fprintf(stdout, "Cannot allocate/free memory for the reserved segment.\n");
    thalt();  
    return;
  }

  if (a) {
    fprintf(stdout, "Heap increase requested by process %hu.\n", cur);
  } else {
    fprintf(stdout, "Heap decrease requested by process %hu.\n", cur);
  }

  uint16_t ptbr  = reg[PTBR];
  uint16_t pte   = mem[ptbr + vpn];
  uint16_t valid = (uint16_t)(pte & 0x0001);

  if (a) {
    if (valid) {
      fprintf(stdout,
              "Cannot allocate memory for page %hu of pid %hu since it is already allocated.\n",
              vpn, cur);
      return;
    }

    uint16_t read_flag  = r ? UINT16_MAX : 0;
    uint16_t write_flag = w ? UINT16_MAX : 0;

    uint16_t res = allocMem(ptbr, vpn, read_flag, write_flag);
    if (res == 0) {
      fprintf(stdout,
              "Cannot allocate more space for pid %hu since there is no free page frames.\n",
              cur);
      return;
    }
    return;

  } else {

    if (!valid) {
      fprintf(stdout,
              "Cannot free memory of page %hu of pid %hu since it is not allocated.\n",
              vpn, cur);
      return;
    }

    freeMem(vpn, ptbr);
    return;
  }
}



static inline void tyld() {
  uint16_t old = mem[Cur_Proc_ID];
  if (old == UINT16_MAX) return;

  uint16_t next = find_next_runnable_excluding_self(old);
  if (next == UINT16_MAX) {

    return;
  }


  uint16_t old_pcb = pcb_addr(old);
  mem[old_pcb + PC_PCB]   = reg[RPC];
  mem[old_pcb + PTBR_PCB] = reg[PTBR];


  loadProc(next);

  fprintf(stdout, "We are switching from process %hu to %hu.\n", old, next);
}




static inline void thalt() {
  uint16_t pid = mem[Cur_Proc_ID];
  if (pid == UINT16_MAX) { running = false; return; }

  uint16_t ptbr = reg[PTBR];
  for (uint16_t vpn = 0; vpn < 32; vpn++) {
    uint16_t pte = mem[ptbr + vpn];
    if (pte & 0x0001) { 
      freeMem(vpn, ptbr);
    }
  }
  uint16_t pcb = pcb_addr(pid);
  mem[pcb + PID_PCB] = UINT16_MAX;
  uint16_t next = find_next_runnable_excluding_self(pid);
  if (next == UINT16_MAX) {

    running = false;
    return;
  }
  loadProc(next);
}


static inline uint16_t mr(uint16_t address) {

  uint16_t vpn    = (uint16_t)(address >> 11);
  uint16_t offset = (uint16_t)(address & 0x07FF);

  if (vpn < CODE_VPN0 || vpn >= 16) {
    fprintf(stdout, "Segmentation fault.\n");
    exit(1);
  }

  uint16_t pte = mem[reg[PTBR] + vpn];

  if ((pte & 0x0001) == 0) {
    fprintf(stdout, "Segmentation fault inside free space.\n");
    exit(1);
  }

  if (((pte >> 1) & 0x1) == 0) {
    fprintf(stdout, "Cannot read the page.\n");
    exit(1);
  }


  uint16_t pfn = (uint16_t)(pte >> 11);

  uint16_t phys = (uint16_t)(pfn * PAGE_SIZE + offset);
  return mem[phys];
}

static inline void mw(uint16_t address, uint16_t val) {

  uint16_t vpn    = (uint16_t)(address >> 11);
  uint16_t offset = (uint16_t)(address & 0x07FF);


  if (vpn < CODE_VPN0 || vpn >= 16) {
    fprintf(stdout, "Segmentation fault.\n");
    exit(1);
  }


  uint16_t pte = mem[reg[PTBR] + vpn];


  if ((pte & 0x0001) == 0) {
    fprintf(stdout, "Segmentation fault inside free space.\n");
    exit(1);
  }


  if (((pte >> 2) & 0x1) == 0) {
    fprintf(stdout, "Cannot write to a read-only page.\n");
    exit(1);
  }

  uint16_t pfn = (uint16_t)(pte >> 11);
  uint16_t phys = (uint16_t)(pfn * PAGE_SIZE + offset);
  mem[phys] = val;
}


// YOUR CODE ENDS HERE
