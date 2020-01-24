/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#include "caml/addrmap.h"
#include "caml/config.h"
#include "caml/custom.h"
#include "caml/domain.h"
#include "caml/eventlog.h"
#include "caml/fail.h"
#include "caml/fiber.h"
#include "caml/finalise.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/major_gc.h"
#include "caml/memory.h"
#include "caml/minor_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/roots.h"
#include "caml/shared_heap.h"
#include "caml/signals.h"
#include "caml/weak.h"

extern value caml_ephe_none; /* See weak.c */
struct generic_table CAML_TABLE_STRUCT(char);

static struct domain* domains_finished_promote[Max_domains];
static atomic_intnat domains_finished_promote_count;
static atomic_intnat domains_participating_in_promotion;

/* [sz] and [rsv] are numbers of entries */
static void alloc_generic_table (struct generic_table *tbl, asize_t sz,
                                 asize_t rsv, asize_t element_size)
{
  void *new_table;

  tbl->size = sz;
  tbl->reserve = rsv;
  new_table = (void *) caml_stat_alloc_noexc((tbl->size + tbl->reserve) *
                                             element_size);
  if (new_table == NULL) caml_fatal_error ("Fatal error: not enough memory\n");
  if (tbl->base != NULL) caml_stat_free (tbl->base);
  tbl->base = new_table;
  tbl->ptr = tbl->base;
  tbl->threshold = tbl->base + tbl->size * element_size;
  tbl->limit = tbl->threshold;
  tbl->end = tbl->base + (tbl->size + tbl->reserve) * element_size;
}

void caml_alloc_table (struct caml_ref_table *tbl, asize_t sz, asize_t rsv)
{
  alloc_generic_table ((struct generic_table *) tbl, sz, rsv, sizeof (value *));
}

static void reset_table (struct generic_table *tbl)
{
  tbl->size = 0;
  tbl->reserve = 0;
  if (tbl->base != NULL) caml_stat_free (tbl->base);
  tbl->base = tbl->ptr = tbl->threshold = tbl->limit = tbl->end = NULL;
}

static void clear_table (struct generic_table *tbl)
{
    tbl->ptr = tbl->base;
    tbl->limit = tbl->threshold;
}

struct caml_minor_tables* caml_alloc_minor_tables()
{
  struct caml_minor_tables *r =
      caml_stat_alloc_noexc(sizeof(struct caml_minor_tables));
  if(r != NULL)
    memset(r, 0, sizeof(*r));
  return r;
}

void reset_minor_tables(struct caml_minor_tables* r)
{
  reset_table((struct generic_table *)&r->major_ref);
  reset_table((struct generic_table *)&r->ephe_ref);
  reset_table((struct generic_table *)&r->custom);
#ifdef DEBUG
  reset_table((struct generic_table *)&r->minor_ref);
#endif
}

void caml_free_minor_tables(struct caml_minor_tables* r)
{
  CAMLassert(r->major_ref.ptr == r->major_ref.base);

  reset_minor_tables(r);
  caml_stat_free(r);
}

void caml_set_minor_heap_size (asize_t wsize)
{
  caml_domain_state* domain_state = Caml_state;
  struct caml_minor_tables *r = domain_state->minor_tables;
  if (domain_state->young_ptr != domain_state->young_end) caml_minor_collection ();

  if(caml_reallocate_minor_heap(wsize) < 0) {
    caml_fatal_error("Fatal error: No memory for minor heap");
  }

  reset_minor_tables(r);
}

//*****************************************************************************

struct oldify_state {
  value todo_list;
  uintnat live_bytes;
  struct domain* promote_domain;
};

static value alloc_shared(mlsize_t wosize, tag_t tag)
{
  void* mem = caml_shared_try_alloc(Caml_state->shared_heap, wosize, tag,
                                    0 /* not pinned */);
  Caml_state->allocated_words += Whsize_wosize(wosize);
  if (mem == NULL) {
    caml_fatal_error("allocation failure during minor GC");
  }
  return Val_hp(mem);
}

static inline int is_in_interval (value v, char* low_closed, char* high_open)
{
  return low_closed <= (char*)v && (char*)v < high_open;
}

static inline void log_gc_value(const char* prefix, value v)
{
  if (Is_block(v)) {
    header_t hd = Hd_val(v);
    int sz = Wosize_hd (hd);
    caml_gc_log("%s 0x%lx hd=0x%lx tag=%d sz=%d", prefix, v, hd, Tag_val(v), sz);
  } else {
    caml_gc_log("%s not block 0x%lx", prefix, v);
  }
}

#define Color_hd(v) ((color_t)(((v) >> 8) & 3))

static int get_header_val(value v) {
  if( caml_domain_alone() ) {
    return Hd_val(v);
  } else {
    header_t hd = atomic_load(Hp_atomic_val(v));

    if ( Wosize_hd(hd) == 0 && Color_hd(hd) == 1 ) {
      while( atomic_load(Hp_atomic_val(v)) != 0 ) {}
      return 0;
    }

    return hd;
  }
}

static inline void spin_on_header(value v) {
  while( atomic_load(Hp_atomic_val(v)) != 0 ) {}
}

static int try_update_object_header(value v, value *p, value result, mlsize_t infix_offset) {
  int success = 0;

  if( caml_domain_alone() ) {
    *Hp_val (v) = 0;
    Op_val(v)[0] = result;
    success = 1;
  } else {
    header_t hd = atomic_load(Hp_atomic_val(v));
    if( hd == 0 ) {
      // in this case this has been updated by another domain, throw away result
      // and return the one in the object
      result = Op_val(v)[0];
    } else if ( Wosize_hd(hd) == 0 && Color_hd(hd) == 1 ) {
      // here we've caught a domain in the process of moving a minor heap object
      // we need to wait for it to finish
      // TODO: Probably a better spinlock needed here though doesn't happen often
      spin_on_header(v);
      // Also throw away result and use the one from the other domain
      result = Op_val(v)[0];
    } else {
      // Here the header is neither zero nor an in-progress update
      header_t desired_hd = 1 << 8; // set the lowest color bit - this should probably be in a macro
      if( atomic_compare_exchange_strong(Hp_atomic_val(v), &hd, desired_hd) ) {
        // Success
        // Now we can write the forwarding pointer
        atomic_store_explicit(Op_atomic_val(v), result, memory_order_relaxed);
        // And can update the header too
        atomic_store_explicit(Hp_atomic_val(v), 0, memory_order_relaxed);
        // Let the caller know we were responsible for the update
        success = 1;
      } else {
        // We were sniped by another domain, spin for that to complete then
        // throw away result and use the one from the other domain
        spin_on_header(v);
        result = Op_val(v)[0];
      }
    }
  }

  *p = result + infix_offset;
  return success;
}

/* If [*v] is an [Infix_tag] object, [v] is updated to point to the first
 * object in the block. */
static inline void resolve_infix_val (value* v)
{
  int offset = 0;
  if (get_header_val(*v) == Infix_tag) {
    offset = Infix_offset_val(*v);
    CAMLassert (offset > 0);
    *v -= offset;
  }
}

/* Note that the tests on the tag depend on the fact that Infix_tag,
   Forward_tag, and No_scan_tag are contiguous. */
static void oldify_one (void* st_v, value v, value *p)
{
  struct oldify_state* st = st_v;
  value result;
  header_t hd;
  mlsize_t sz, i;
  mlsize_t infix_offset;
  tag_t tag;

  tail_call:
  if (!(Is_block(v) && Is_minor(v))) {
    /* not a minor block */
    *p = v;
    return;
  }

  infix_offset = 0;
  do {
    hd = get_header_val(v);
    if (hd == 0) {
      /* already forwarded, another domain is likely working on this. */
      *p = Op_val(v)[0] + infix_offset;
      return;
    }
    tag = Tag_hd (hd);
    if (tag == Infix_tag) {
      /* Infix header, retry with the real block */
      CAMLassert (infix_offset == 0);
      infix_offset = Infix_offset_hd (hd);
      CAMLassert(infix_offset > 0);
      v -= infix_offset;
    }
  } while (tag == Infix_tag);

  if (tag == Cont_tag) {
    struct stack_info* stk = Ptr_val(Op_val(v)[0]);
    CAMLassert(Wosize_hd(hd) == 1 && infix_offset == 0);
    result = alloc_shared(1, Cont_tag);
    if( try_update_object_header(v, p, result, 0) ) {
      Op_val(result)[0] = Val_ptr(stk);
      if (stk != NULL) {
        caml_scan_stack(&oldify_one, st, stk);
      }
    }
    else
    {
      // Conflict - fix up what we allocated on the major heap
      *Hp_val(result) = Make_header(1, No_scan_tag, global.MARKED);
      #ifdef DEBUG
      Op_val(result)[0] = Val_long(1);
      #endif
    }
  } else if (tag < Infix_tag) {
    value field0;
    sz = Wosize_hd (hd);
    st->live_bytes += Bhsize_hd(hd);
    result = alloc_shared (sz, tag);
    field0 = Op_val(v)[0];
    if( try_update_object_header(v, p, result, infix_offset) ) {
      if (sz > 1){
        Op_val (result)[0] = field0;
        Op_val (result)[1] = st->todo_list;
        st->todo_list = v;
      } else {
        CAMLassert (sz == 1);
        p = Op_val(result);
        v = field0;
        goto tail_call;
      }
    } else {
      // Conflict - fix up what we allocated on the major heap
      *Hp_val(result) = Make_header(sz, No_scan_tag, global.MARKED);
      #ifdef DEBUG
      {
        for( i = 0; i < sz ; i++ ) {
          Op_val(result)[i] = Val_long(1);
        }
      }
      #endif
    }

  } else if (tag >= No_scan_tag) {
    sz = Wosize_hd (hd);
    st->live_bytes += Bhsize_hd(hd);
    result = alloc_shared(sz, tag);
    for (i = 0; i < sz; i++) {
      value curr = Op_val(v)[i];
      Op_val (result)[i] = curr;
    }
    CAMLassert (infix_offset == 0);
    if( !try_update_object_header(v, p, result, 0) ) {
      // Conflict
      *Hp_val(result) = Make_header(sz, No_scan_tag, global.MARKED);
      #ifdef DEBUG
      for( i = 0; i < sz ; i++ ) {
        Op_val(result)[i] = Val_long(1);
      }
      #endif
    }
  } else {
    CAMLassert (tag == Forward_tag);
    CAMLassert (infix_offset == 0);

    value f = Forward_val (v);
    tag_t ft = 0;

    if (Is_block (f)) {
      ft = Tag_val (get_header_val(f) == 0 ? Op_val (f)[0] : f);
    }

    if (ft == Forward_tag || ft == Lazy_tag || ft == Double_tag) {
      /* Do not short-circuit the pointer.  Copy as a normal block. */
      CAMLassert (Wosize_hd (hd) == 1);
      st->live_bytes += Bhsize_hd(hd);
      result = alloc_shared (1, Forward_tag);
      if( try_update_object_header(v, p, result, 0) ) {
        p = Op_val (result);
        v = f;
        goto tail_call;
      } else {
        *Hp_val(result) = Make_header(1, No_scan_tag, global.MARKED);
        #ifdef DEBUG
        Op_val(result)[0] = Val_long(1);
        #endif
      }
    } else {
      v = f;                        /* Follow the forwarding */
      goto tail_call;               /*  then oldify. */
    }
  }
}

/* Test if the ephemeron is alive */
static inline int ephe_check_alive_data (struct caml_ephe_ref_elt *re,
                                         char* young_ptr, char* young_end)
{
  mlsize_t i;
  value child;

  for (i = CAML_EPHE_FIRST_KEY; i < Wosize_val(re->ephe); i++) {
    child = Op_val(re->ephe)[i];
    if (child != caml_ephe_none
        && Is_block (child) && Is_minor(child)) {
      resolve_infix_val(&child);
      if (get_header_val(child) != 0) {
        /* value not copied to major heap */
        return 0;
      }
    }
  }

  return 1;
}

int workshare_offer_buffer(struct domain* other_domain, struct caml_minor_work* offered_buffer) {
  caml_domain_state* domain_state = other_domain->state;

  intnat tmp_state = atomic_load_explicit(&domain_state->workshare_state, memory_order_relaxed);

  if( tmp_state == 0 ) {
    // Try to get ownership of this buffer
    if( atomic_compare_exchange_strong(&domain_state->workshare_state, &tmp_state, 1) ) {
        memcpy(&domain_state->workshare_buffer, offered_buffer, WORKSHARE_BUFFER_SIZE * sizeof(struct caml_minor_work));

        atomic_thread_fence(memory_order_release);
        atomic_store_explicit(&domain_state->workshare_state, 2, memory_order_release);

        return 1;
    }
  }
  
  return 0;
}

int workshare_try_read_buffer(struct caml_minor_work* private_buffer) {
  caml_domain_state* domain_state = Caml_state;

  if( atomic_load_explicit(&domain_state->workshare_state, memory_order_acquire) == 2 ) {
      memcpy(private_buffer, &domain_state->workshare_buffer, WORKSHARE_BUFFER_SIZE * sizeof(struct caml_minor_work));
      atomic_thread_fence(memory_order_acquire);
      atomic_store_explicit(&domain_state->workshare_state, 0, memory_order_release);
      return 1;
  }

  return 0;
}

static void oldify_mopup (struct oldify_state* st, int workshare, int check_ephemerons);

int share_work_buffer(struct caml_minor_work* buffer) {
  int d, s;
  int finished_count = atomic_load_explicit(&domains_finished_promote_count, memory_order_acquire);

  CAMLassert(domains_finished_promote_count >= 0);

  // TODO: Probably need some heuristic here for how many domains should be finished before we start
  // trying to farm off work
  if( finished_count == 0 ) return 0;

  s = (rand() % finished_count);
  d = s;
  do {
    if( workshare_offer_buffer(domains_finished_promote[d], buffer) )
    {
      return 1;
    }
    d = (s++) % finished_count; // TODO: We should probably not do the entire lot, maybe only advance a couple?
  } while( d != s );

  return 0;
}

void process_workshare_buffer(struct caml_minor_work* buffer, int work_count) {
  struct oldify_state st = {0};
  int c;
  
  for( c = 0 ; c < work_count ; c++ ) {
    oldify_one(&st, buffer[c].v, buffer[c].p);
  }

  oldify_mopup(&st, 0 /* don't workshare */, 0);
}

void add_to_work_buffer(struct caml_minor_work* buffer, int* work_count, value v, value* p) {
  if( *work_count == WORKSHARE_BUFFER_SIZE ) {
    printf("trying to share buffer..\n");
    if( share_work_buffer(buffer) ) {
      printf("shared buffer..\n");
      *work_count = 0;
    }
    else 
    {
      // In this case we didn't manage to share the buffer, so we should just do the work ourselves
      process_workshare_buffer(buffer, WORKSHARE_BUFFER_SIZE);
    }
  }
  buffer[*work_count].p = p;
  buffer[*work_count].v = v;

  printf("work_count: %d\n", *work_count);
  *work_count = *work_count + 1;
}

/* Finish the work that was put off by [oldify_one].
   Note that [oldify_one] itself is called by oldify_mopup, so we
   have to be careful to remove the first entry from the list before
   oldifying its fields. */
static void oldify_mopup (struct oldify_state* st, int workshare, int do_ephemerons)
{
  struct caml_minor_work work_buffer[WORKSHARE_BUFFER_SIZE];
  int work_count = 0;

  value v, new_v, f;
  mlsize_t i;
  caml_domain_state* domain_state =
    st->promote_domain ? st->promote_domain->state : Caml_state;
  struct caml_ephe_ref_table ephe_ref_table = domain_state->minor_tables->ephe_ref;
  struct caml_ephe_ref_elt *re;
  char* young_ptr = domain_state->young_ptr;
  char* young_end = domain_state->young_end;
  int redo = 0;
  int is_alone = caml_domain_alone();

  while (st->todo_list != 0) {
    v = st->todo_list;                 /* Get the head. */
    /* I'm not convinced we can ever have something in todo_list that was updated
    by another domain, so this assert using get_header_val is probably not
    neccessary */
    CAMLassert (get_header_val(v) == 0);       /* It must be forwarded. */
    new_v = Op_val (v)[0];                /* Follow forward pointer. */
    st->todo_list = Op_val (new_v)[1]; /* Remove from list. */

    f = Op_val (new_v)[0];
    CAMLassert (!Is_debug_tag(f));
    if (Is_block (f) && Is_minor(f)) {
      if( !is_alone && workshare ) {
        add_to_work_buffer(work_buffer, &work_count, f, Op_val(new_v));
      } else {
        oldify_one(st, f, Op_val(new_v));
      }
    }
    for (i = 1; i < Wosize_val (new_v); i++){
      f = Op_val (v)[i];
      CAMLassert (!Is_debug_tag(f));
      if (Is_block (f) && Is_minor(f)) {
        if( !is_alone && workshare ) {
          add_to_work_buffer(work_buffer, &work_count, f, Op_val(new_v) + i);
        } else {
          oldify_one(st, f, Op_val(new_v) + i);
        }
      } else {
        Op_val (new_v)[i] = f;
      }
    }
    CAMLassert (Wosize_val(new_v));
  }

  if( !is_alone && workshare ) {
    process_workshare_buffer(work_buffer, work_count);
  }

  if( do_ephemerons ) {
    /* Oldify the data in the minor heap of alive ephemeron
      During minor collection keys outside the minor heap are considered alive */
    for (re = ephe_ref_table.base;
        re < ephe_ref_table.ptr; re++) {
      /* look only at ephemeron with data in the minor heap */
      if (re->offset == CAML_EPHE_DATA_OFFSET) {
        value *data = &Ephe_data(re->ephe);
        if (*data != caml_ephe_none && Is_block(*data) && Is_minor(*data) ) {
          resolve_infix_val(data);
          if (get_header_val(*data) == 0) { /* Value copied to major heap */
            *data = Op_val(*data)[0];
          } else {
            if (ephe_check_alive_data(re, young_ptr, young_end)) {
              oldify_one(st, *data, data);
              redo = 1; /* oldify_todo_list can still be 0 */
            }
          }
        }
      }
    }
  }

  if (redo) oldify_mopup (st, 0, 1);
}

//*****************************************************************************

static value next_minor_block(caml_domain_state* domain_state, value curr_hp)
{
  mlsize_t wsz;
  header_t hd;
  value curr_val;
  CAMLassert ((value)domain_state->young_ptr <= curr_hp);
  CAMLassert (curr_hp < (value)domain_state->young_end);
  hd = Hd_hp(curr_hp);
  curr_val = Val_hp(curr_hp);
  if (hd == 0) {
    /* Forwarded object, find the promoted version */
    curr_val = Op_val(curr_val)[0];
  }
  CAMLassert (Is_block(curr_val) && Hd_val(curr_val) != 0 && Tag_val(curr_val) != Infix_tag);
  wsz = Wosize_val(curr_val);
  CAMLassert (wsz <= Max_young_wosize);
  return curr_hp + Bsize_wsize(Whsize_wosize(wsz));
}

CAMLexport value caml_promote(struct domain* domain, value root)
{
  return root;
}

//*****************************************************************************

void caml_empty_minor_heap_domain_finalizers (struct domain* domain, void* unused)
{
  caml_domain_state* domain_state = domain->state;
  struct caml_minor_tables *minor_tables = domain_state->minor_tables;
  struct caml_custom_elt *elt;

  caml_ev_begin("minor_gc/finalisers");
  caml_final_update_last_minor(domain);
  /* Run custom block finalisation of dead minor values */
  for (elt = minor_tables->custom.base; elt < minor_tables->custom.ptr; elt++) {
    value v = elt->block;
    if (Hd_val(v) == 0) {
      /* !!caml_adjust_gc_speed(elt->mem, elt->max); */
    } else {
      /* Block will be freed: call finalisation function, if any */
      void (*final_fun)(value) = Custom_ops_val(v)->finalize;
      if (final_fun != NULL) final_fun(v);
    }
  }
  caml_ev_end("minor_gc/finalisers");
}

void caml_empty_minor_heap_domain_clear (struct domain* domain, void* unused)
{
  caml_domain_state* domain_state = domain->state;
  struct caml_minor_tables *minor_tables = domain_state->minor_tables;

  caml_final_empty_young(domain);

  clear_table ((struct generic_table *)&minor_tables->major_ref);
  clear_table ((struct generic_table *)&minor_tables->ephe_ref);
  clear_table ((struct generic_table *)&minor_tables->custom);
#ifdef DEBUG
  clear_table ((struct generic_table *)&minor_tables->minor_ref);
#endif

  domain_state->young_ptr = domain_state->young_end;
}

void caml_empty_minor_heap_promote (struct domain* domain, void* unused)
{
  caml_domain_state* domain_state = domain->state;
  struct caml_minor_tables *minor_tables = domain_state->minor_tables;
  unsigned rewrite_successes = 0;
  unsigned rewrite_failures = 0;
  char* young_ptr = domain_state->young_ptr;
  char* young_end = domain_state->young_end;
  uintnat minor_allocated_bytes = young_end - young_ptr;
  struct oldify_state st = {0};
  value **r;

  st.promote_domain = domain;

  /* TODO: are there any optimizations we can make where we don't need to scan
     when minor heaps can reference each other? */
  uintnat prev_alloc_words = domain_state->allocated_words;

  caml_gc_log ("Minor collection of domain %d starting", domain->state->id);
  caml_ev_begin("minor_gc");
  caml_ev_begin("minor_gc/roots");
  caml_do_local_roots(&oldify_one, &st, domain, 0);
  caml_scan_stack(&oldify_one, &st, domain_state->current_stack);

  for (r = minor_tables->major_ref.base; r < minor_tables->major_ref.ptr; r++) {
    oldify_one (&st, **r, *r);
  }
  caml_ev_end("minor_gc/roots");

  caml_ev_begin("minor_gc/promote");
  oldify_mopup (&st, 1, 0);
  caml_ev_end("minor_gc/promote");


#ifdef DEBUG
  for (r = minor_tables->major_ref.base;
       r < minor_tables->major_ref.ptr; r++) {
    value vnew = **r;
    CAMLassert (!Is_block(vnew) || (!Is_minor(vnew) && Hd_val(vnew) != 0));
  }
#endif

  domain_state->stat_minor_words += Wsize_bsize (minor_allocated_bytes);
  domain_state->stat_minor_collections++;
  domain_state->stat_promoted_words += domain_state->allocated_words - prev_alloc_words;

  caml_ev_end("minor_gc");
  caml_gc_log ("Minor collection of domain %d completed: %2.0f%% of %u KB live, rewrite: successes=%u failures=%u",
               domain->state->id,
               100.0 * (double)st.live_bytes / (double)minor_allocated_bytes,
               (unsigned)(minor_allocated_bytes + 512)/1024, rewrite_successes, rewrite_failures);
}

void caml_final_oldify_cleanup (struct domain* domain) {
  struct oldify_state st = {0};
  struct caml_ephe_ref_elt *re;
  caml_domain_state* domain_state = domain->state;
  struct caml_minor_tables *minor_tables = domain_state->minor_tables;  
  int is_alone = caml_domain_alone();

  caml_ev_begin("minor_gc/oldify_cleanup");

  if( !is_alone ) {
    struct caml_minor_work buffer[WORKSHARE_BUFFER_SIZE];

    if( workshare_try_read_buffer(buffer) ) {
      process_workshare_buffer(buffer, WORKSHARE_BUFFER_SIZE);
    }
  }

  oldify_mopup(&st, 0, 1);

  caml_ev_end("minor_gc/oldify_cleanup");

  caml_ev_begin("minor_gc/ephemerons");
  for (re = minor_tables->ephe_ref.base;
       re < minor_tables->ephe_ref.ptr; re++) {
    CAMLassert (Ephe_domain(re->ephe) == domain);
    if (re->offset == CAML_EPHE_DATA_OFFSET) {
      /* Data field has already been handled in oldify_mopup. Handle only
       * keys here. */
      continue;
    }
    value* key = &Op_val(re->ephe)[re->offset];
    if (*key != caml_ephe_none && Is_block(*key) && Is_minor(*key)) {
      resolve_infix_val(key);
      if (get_header_val(*key) == 0) { /* value copied to major heap */
        *key = Op_val(*key)[0];
      } else {
        // CAMLassert(!ephe_check_alive_data(re,young_ptr,young_end));
        *key = caml_ephe_none;
        Ephe_data(re->ephe) = caml_ephe_none;
      }
    }
  }
  caml_ev_end("minor_gc/ephemerons");
}

void caml_participate_in_promotion(struct domain* domain) {
  struct caml_minor_work buffer[WORKSHARE_BUFFER_SIZE];

  caml_ev_begin("minor_gc/workshare");

  while( atomic_load_explicit(&domains_participating_in_promotion, memory_order_acquire) > atomic_load_explicit(&domains_finished_promote_count, memory_order_acquire) ) {
    if( workshare_try_read_buffer(buffer) ) {
      caml_ev_begin("minor_gc/workshare/process");
      printf("processing workshare buffer\n");
      process_workshare_buffer(buffer, WORKSHARE_BUFFER_SIZE);
      caml_ev_end("minor_gc/workshare/process");
    } else {
      // TODO: probably worth backing off here..
    }
  }

  caml_ev_end("minor_gc/workshare");
}

/* must be called within a STW section */
void caml_stw_empty_minor_heap (struct domain* domain, void* unused)
{
  #ifdef DEBUG
  CAMLassert(caml_domain_is_in_stw());
  #endif

  barrier_status b;

  b = caml_global_barrier_begin();
  if( caml_global_barrier_is_final(b) ) {
    int c;
    for( c = 0; c < Max_domains ; c++ ) {
      domains_finished_promote[c] = NULL;
    }

    atomic_store_explicit(&domains_finished_promote_count, 0, memory_order_release);
    atomic_store_explicit(&domains_participating_in_promotion, 0, memory_order_release);
  }
  caml_global_barrier_end(b);
 
  atomic_fetch_add_explicit(&domains_participating_in_promotion, 1, memory_order_acq_rel);
  caml_gc_log("running stw empty_minor_heap_promote");
  caml_empty_minor_heap_promote(domain, 0);

  int is_alone = caml_domain_alone();

  // if we're not alone, start worksharing if we finish a promote early
  if( !is_alone ) {
    intnat finished_count = atomic_fetch_add_explicit(&domains_finished_promote_count, 1, memory_order_acq_rel);
    domains_finished_promote[finished_count] = caml_domain_self();
    atomic_thread_fence(memory_order_release);
    caml_participate_in_promotion(domain);

    b = caml_global_barrier_begin();
    caml_global_barrier_end(b);
  }

  caml_final_oldify_cleanup(domain);

  b = caml_global_barrier_begin();

  if( caml_global_barrier_is_final(b) ) {
    caml_ev_begin("minor_gc/finalizers");
    caml_gc_log("running stw empty_minor_heap_domain_finalizers");
    caml_run_on_all_running_domains_during_stw(&caml_empty_minor_heap_domain_finalizers, (void*)0);
    caml_ev_end("minor_gc/finalizers");
    caml_ev_begin("minor_gc/clear");
    caml_gc_log("running stw empty_minor_heap_domain_clear");
    caml_run_on_all_running_domains_during_stw(&caml_empty_minor_heap_domain_clear, (void*)0);
    caml_ev_end("minor_gc/clear");
    caml_gc_log("finished stw empty_minor_heap");
  }

  caml_global_barrier_end(b);
}

/* must be called outside a STW section */
int caml_try_stw_empty_minor_heap_on_all_domains ()
{
  #ifdef DEBUG
  CAMLassert(!caml_domain_is_in_stw());
  #endif

  caml_gc_log("requesting stw empty_minor_heap");
  return caml_try_run_on_all_domains(&caml_stw_empty_minor_heap, (void*)0);
}

/* must be called outside a STW section, will retry until we have emptied our minor heap */
void caml_empty_minor_heaps_once ()
{
  #ifdef DEBUG
  CAMLassert(!caml_domain_is_in_stw());
  #endif

  while( !caml_try_stw_empty_minor_heap_on_all_domains() )
    ;
}

/* Do a minor collection and a slice of major collection, call finalisation
   functions, etc.
   Leave the minor heap empty.
*/
CAMLexport void caml_minor_collection (void)
{
  caml_ev_pause(EV_PAUSE_GC);

  caml_handle_incoming_interrupts ();
  caml_try_stw_empty_minor_heap_on_all_domains();
  /* TODO: is try really acceptable or do we need 'every time'
  caml_empty_minor_heap (); */
  caml_handle_incoming_interrupts ();
  caml_major_collection_slice (0, 0);
  caml_final_do_calls();

  caml_ev_resume();

  /* If the major slice triggered a STW, do that now */
  caml_handle_gc_interrupt();
}

CAMLexport value caml_check_urgent_gc (value extra_root)
{
  CAMLparam1 (extra_root);
  caml_handle_gc_interrupt();
  CAMLreturn (extra_root);
}

static void realloc_generic_table
(struct generic_table *tbl, asize_t element_size,
 char * msg_intr_int, char *msg_threshold, char *msg_growing, char *msg_error)
{
  CAMLassert (tbl->ptr == tbl->limit);
  CAMLassert (tbl->limit <= tbl->end);
  CAMLassert (tbl->limit >= tbl->threshold);

  if (tbl->base == NULL){
    alloc_generic_table (tbl, Caml_state->minor_heap_wsz / 8, 256,
                         element_size);
  }else if (tbl->limit == tbl->threshold){
    CAML_INSTR_INT (msg_intr_int, 1);
    caml_gc_message (0x08, msg_threshold, 0);
    tbl->limit = tbl->end;
    caml_urge_major_slice ();
  }else{
    asize_t sz;
    asize_t cur_ptr = tbl->ptr - tbl->base;

    tbl->size *= 2;
    sz = (tbl->size + tbl->reserve) * element_size;
    caml_gc_message (0x08, msg_growing, (intnat) sz/1024);
    tbl->base = caml_stat_resize_noexc (tbl->base, sz);
    if (tbl->base == NULL){
      caml_fatal_error (msg_error);
    }
    tbl->end = tbl->base + (tbl->size + tbl->reserve) * element_size;
    tbl->threshold = tbl->base + tbl->size * element_size;
    tbl->ptr = tbl->base + cur_ptr;
    tbl->limit = tbl->end;
  }
}

void caml_realloc_ref_table (struct caml_ref_table *tbl)
{
  realloc_generic_table
    ((struct generic_table *) tbl, sizeof (value *),
     "request_minor/realloc_ref_table@",
     "ref_table threshold crossed\n",
     "Growing ref_table to %" ARCH_INTNAT_PRINTF_FORMAT "dk bytes\n",
     "Fatal error: ref_table overflow\n");
}

void caml_realloc_ephe_ref_table (struct caml_ephe_ref_table *tbl)
{
  realloc_generic_table
    ((struct generic_table *) tbl, sizeof (struct caml_ephe_ref_elt),
     "request_minor/realloc_ephe_ref_table@",
     "ephe_ref_table threshold crossed\n",
     "Growing ephe_ref_table to %" ARCH_INTNAT_PRINTF_FORMAT "dk bytes\n",
     "Fatal error: ephe_ref_table overflow\n");
}

void caml_realloc_custom_table (struct caml_custom_table *tbl)
{
  realloc_generic_table
    ((struct generic_table *) tbl, sizeof (struct caml_custom_elt),
     "request_minor/realloc_custom_table@",
     "custom_table threshold crossed\n",
     "Growing custom_table to %" ARCH_INTNAT_PRINTF_FORMAT "dk bytes\n",
     "custom_table overflow");
}
