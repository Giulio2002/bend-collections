#ifndef DLIST_ITERATOR_H
#define DLIST_ITERATOR_H
#include "dlist_arena.h"
/* Exclusive owning gap cursor. Moving from a St transfers its arena; the
 * source cannot be used until it_finish returns it. C callers obey the move
 * contract explicitly; Bend enforces it through affine ownership. */
typedef struct {St list;uint32_t next,last,index;int forward;} DIterator;
enum IterStatus {ITER_OK=0,ITER_END=1,ITER_NO_CURRENT=2};
static DIterator it_first(St *source){DIterator it={.list=*source,.next=source->head,.last=NO_ID,.index=0,.forward=1};memset(source,0,sizeof(*source));return it;}
static DIterator it_last(St *source){DIterator it=it_first(source);it.next=NO_ID;it.index=it.list.count;return it;}
static St it_finish(DIterator *it){St s=it->list;memset(it,0,sizeof(*it));return s;}
static int it_has_next(const DIterator*it){return it->next!=NO_ID;}
static int it_has_previous(const DIterator*it){return it->index!=0;}
static enum IterStatus it_next(DIterator*it,uint32_t*out){if(it->next==NO_ID)return ITER_END;uint32_t id=it->next;Node*n=&it->list.cells[id];*out=n->val;it->next=n->next;it->last=id;it->forward=1;it->index++;return ITER_OK;}
static enum IterStatus it_previous(DIterator*it,uint32_t*out){uint32_t id=it->next==NO_ID?it->list.tail:it->list.cells[it->next].prev;if(id==NO_ID)return ITER_END;*out=it->list.cells[id].val;it->next=id;it->last=id;it->forward=0;it->index--;return ITER_OK;}
static enum IterStatus it_set(DIterator*it,uint32_t x){if(it->last==NO_ID)return ITER_NO_CURRENT;it->list.cells[it->last].val=x;return ITER_OK;}
static enum IterStatus it_add(DIterator*it,uint32_t x){uint32_t prev=it->next==NO_ID?it->list.tail:it->list.cells[it->next].prev;insert_between(&it->list,prev,it->next,x);it->index++;it->last=NO_ID;return ITER_OK;}
static enum IterStatus it_remove(DIterator*it){if(it->last==NO_ID)return ITER_NO_CURRENT;it->next=it->list.cells[it->last].next;remove_node(&it->list,it->last);if(it->forward)it->index--;it->last=NO_ID;return ITER_OK;}
#endif
