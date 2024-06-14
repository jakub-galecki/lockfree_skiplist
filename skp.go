package lockfree_skiplist

/*
Implementation based on:
	Maurice Herlihy and Nir Shavit. 2012. The Art of Multiprocessor Programming,
	Revised Reprint (1st. ed.). Morgan Kaufmann Publishers Inc., San Francisco, CA, USA.
*/

import (
	"cmp"
	"math/rand"
	"sync/atomic"
)

type markableRef[T any] struct {
	ref    *T
	marked bool
}

func newMarkableRef[T any](ref *T, marked bool) *markableRef[T] {
	return &markableRef[T]{ref, marked}
}

type atomicMarkableRef[T any] struct {
	ref *atomic.Pointer[markableRef[T]]
}

func newAtomicMarkableRef[T any](ref *T, marked bool) *atomicMarkableRef[T] {
	ptr := &atomic.Pointer[markableRef[T]]{}
	ptr.Store(newMarkableRef(ref, marked))
	return &atomicMarkableRef[T]{ref: ptr}
}

func (a *atomicMarkableRef[T]) getRef() *T {
	return a.ref.Load().ref
}

func (a *atomicMarkableRef[T]) getMark() bool {
	return a.ref.Load().marked
}

func (a *atomicMarkableRef[T]) get(mark *bool) *T {
	cur := a.ref.Load()
	*mark = cur.marked
	return cur.ref
}

func (a *atomicMarkableRef[T]) set(ref *T, marked bool) {
	cur := a.ref.Load()
	if cur.ref != ref || cur.marked != marked {
		a.ref.Store(newMarkableRef(ref, marked))
	}
}

func (a *atomicMarkableRef[T]) setMark(marked bool) {
	cur := a.ref.Load()
	if cur.marked != marked {
		a.ref.Store(newMarkableRef(cur.ref, marked))
	}
}

func (a *atomicMarkableRef[T]) compAndSet(expectedRef, newRef *T, expectedMark, newMark bool) bool {
	cur := a.ref.Load()
	if expectedRef != cur.ref && expectedMark != cur.marked {
		return false
	}
	if newRef == cur.ref && newMark == cur.marked {
		return true
	}
	return a.ref.CompareAndSwap(cur, newMarkableRef(newRef, newMark))
}

type node[T cmp.Ordered] struct {
	key,
	value T
	forwards []*atomicMarkableRef[node[T]]
	level    int
}

func newNode[T cmp.Ordered](key, value T, level int) *node[T] {
	res := &node[T]{
		key:      key,
		value:    value,
		forwards: make([]*atomicMarkableRef[node[T]], level+1),
		level:    level,
	}
	for i := range res.forwards {
		res.forwards[i] = newAtomicMarkableRef(&node[T]{}, false)
	}
	return res
}

func newSentinelNode[T cmp.Ordered](level int) *node[T] {
	res := &node[T]{
		forwards: make([]*atomicMarkableRef[node[T]], level),
	}
	for i := range res.forwards {
		res.forwards[i] = newAtomicMarkableRef(&node[T]{}, false)
	}
	return res
}

type SkipList[T cmp.Ordered] struct {
	maxLevel int
	head     *node[T]
	tail     *node[T]
}

func NewSkipList[T cmp.Ordered](maxLvl int) *SkipList[T] {
	skp := &SkipList[T]{maxLevel: maxLvl}
	// todo:   min max value for sentinels
	skp.head = newSentinelNode[T](maxLvl)
	skp.tail = newSentinelNode[T](maxLvl)
	for i := range skp.head.forwards {
		skp.head.forwards[i].set(skp.tail, false)
	}
	return skp
}

func (skp *SkipList[T]) find(key T, preds, succs []*node[T]) bool {
	var (
		marked,
		snip bool

		pred, curr, succ *node[T]
	)
RETRY:
	pred = skp.head
	for i := skp.maxLevel; i >= 0; i-- {
		curr = pred.forwards[i].getRef()
		for {
			succ = curr.forwards[i].get(&marked)
			for marked {
				snip = pred.forwards[i].compAndSet(curr, succ, false, false)
				if !snip {
					continue RETRY
				}
				curr = pred.forwards[i].getRef()
				succ = curr.forwards[i].get(&marked)
			}
			if cmp.Less(curr.key, key) {
				pred = curr
				curr = succ
			} else {
				break
			}
		}
		preds[i] = pred
		succs[i] = curr
	}
	return curr.key == key
}

func (skp *SkipList[T]) Set(key, value T) {
	var (
		topLevel = randomLevel(skp.maxLevel)
		preds    = make([]*node[T], skp.maxLevel+1)
		succs    = make([]*node[T], skp.maxLevel+1)
		nd       = newNode(key, value, topLevel)
	)

	for {
		found := skp.find(key, preds, succs)
		if found {
			nd = nil
			return
		}
		for i := 0; i < topLevel; i++ {
			succ := succs[i]
			nd.forwards[i].set(succ, false)
		}

		pred := preds[0]
		succ := succs[0]
		nd.forwards[0].set(succ, false)
		if !pred.forwards[0].compAndSet(succ, nd, false, false) {
			continue
		}
		for i := 1; i < topLevel; i++ {
			for {
				pred = preds[i]
				succ = succs[i]
				if pred.forwards[i].compAndSet(succ, nd, false, false) {
					break
				}
				_ = skp.find(key, preds, succs)
			}
		}
		return
	}
}

func (skp *SkipList[T]) Delete(key T) bool {
	var (
		preds = make([]*node[T], skp.maxLevel+1)
		succs = make([]*node[T], skp.maxLevel+1)
		succ  *node[T]
	)
	for {
		found := skp.find(key, preds, succs)
		if !found {
			return false
		}
		toRemove := succs[0]
		marked := false
		for i := toRemove.level - 1; i >= 1; i-- {
			succ = toRemove.forwards[i].get(&marked)
			for !marked {
				toRemove.forwards[i].setMark(true)
				succ = toRemove.forwards[i].get(&marked)
			}
		}
		marked = false
		succ = toRemove.forwards[0].get(&marked)
		for {
			iMarkedIt := toRemove.forwards[0].compAndSet(succ, succ, false, true)
			if iMarkedIt {
				return true
			} else if marked {
				return false
			}
		}
	}
}

func randomLevel(maxLevel int) int {
	lvl := 1
	for lvl < maxLevel && rand.Intn(4) == 0 {
		lvl++
	}
	return lvl
}
