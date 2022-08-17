// mem.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

#define MFLN (__LINE__|msgfile)

struct memblk {
  ub4 magic;
  ub4 elsize;
  void *base;
  size_t elems;
  ub8 stamp;
  ub4 fln;
  ub4 seq;
  ub4 mmap;
  ub4 desclen;
  const char *selems;
  const char *selsize;
  char desc[256];
};
typedef struct memblk block;

enum Blkopts { Noinit, Init0, Init1 };

#define alloc(cnt,el,fill,desc,arg) (el*)alloc_fln((cnt),sizeof(el),#cnt,#el,(fill),0,(desc),#arg,(arg),MFLN)
#define talloc(cnt,el,fill,desc,arg) (el*)alloc_fln((cnt),sizeof(el),#cnt,#el,(fill),1,(desc),#arg,(arg),MFLN)

#define alloc0(cnt,el,fill) (el*)alloc_fln((cnt),sizeof(el),#cnt,#el,(fill),0,"","",0,MFLN)
#define talloc0(cnt,el,fill) (el*)alloc_fln((cnt),sizeof(el),#cnt,#el,(fill),1,"","",0,MFLN)

#define mkblock(blk,cnt,el,opt,...) (el*)mkblock_fln((blk),(cnt),sizeof(el),(opt),#cnt,#el,MFLN,__VA_ARGS__)
#define trimblock(blk,cnt,el) (el*)trimblock_fln((blk),(cnt),sizeof(el),#cnt,#el,MFLN)

#define afree(ptr,desc) afree_fln((ptr),MFLN,(desc))
#define afree0(ptr) afree_fln((ptr),MFLN,#ptr)

#define blkdata(blk,pos,el) (el*)(blk)->base + (pos)

#define bound(blk,pos,el) bound_fln((blk),(pos),sizeof(el),#pos,#el,MFLN)
#define boundfln(fln,blk,pos,el) bound_fln((blk),(pos),sizeof(el),#pos,#el,(fln))
#define boundcc(cc,blk,pos,el) if (cc) bound_fln((blk),(pos),sizeof(el),#pos,#el,MFLN)

extern void *alloc_fln(size_t elems,ub4 elsize,const char *slen,const char *sel,ub1 fill,ub4 tmp,const char *desc,const char *sarg,size_t arg,ub4 fln);
extern int afree_fln(void *p,ub4 fln, const char *desc);

extern void * __attribute__ ((format (printf,8,9))) mkblock_fln(block *blk,size_t elems,ub4 elsize,enum Blkopts opts,const char *selems,const char *selsize,ub4 fln,const char *fmt,...);
extern void bound_fln(block *blk,size_t pos,ub4 elsize,const char *spos,const char *sel,ub4 fln);
extern void * trimblock_fln(block *blk,size_t elems,ub4 elsize,const char *selems,const char *selsize,ub4 fln);

extern void showmemsums(void);
extern void achktmpfree(void);

extern size_t nearblock(size_t adr);

extern ub4 meminfo(void);
extern int memrdonly(void *p,size_t len);
extern int mempgin(void);

extern void memcfg(ub4 maxvm,ub4 rep);

extern void inimem(void);
extern void eximem(void);
