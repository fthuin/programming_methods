/*
** Specifications in JML by Florian THUIN (SINF21MS/G - 06561100) and Symeon MALENGREAU (SINF22MS/G - 57121100)
 ** LINGI2224 - Programming methods 2015-2016
 ** Assignment 2, April 01, 2016
 */

/**
 * A bounded set (of integers), implemented as an ordered array where elements
 * are kept sorted.
 */
public class Set {

    /* * * * * *
     * Fields  *
     * * * * * */
    private /*@spec_public@*/ int[] data;
    private /*@spec_public@*/int size;

    /* * * * * * * * * * *
     * Class invariants  *
     * * * * * * * * * * */

    // data must never be null
    //@ invariant data != null;
    // the size should be non-negative and not greater than data.length
    //@ invariant 0 <= size && size <= data.length;
    // the array must be sorted in ascending order without duplicates
    //@ invariant (\forall int i, j; 0 <= i && i < j && j < size; data[i] < data[j]);
    // The owner of data is this object
    //@ invariant data.owner == this;

    /**
     * Return an empty set with a capacity of max elements (max >= 0).
     */
    /*@
      @ modifies data;
      @ modifies size;
      @ // the data structure length should be a positive integer
      @ requires 0 <= max;
      @ // the queue is empty at first
      @ ensures size == 0;
      @ // the data structure length must be of size 'max'
      @ ensures data.length == max;
      @*/
    public Set(int max) {
        this.data = new int[max];
        //@ set data.owner = this;
        this.size = 0;
    }

    /**
     * Return the size of the queue.
     */
    /*@
     @ // The result should be the current size of the queue
     @ ensures \result == size;
     @*/
    public /*@pure@*/ int size() {
        return size;
    }

    /**
     * Return element at index {n}.
     */
    /*@
     @ // n should be in the bounds of the data stored
     @ requires 0 <= n && n < size;
     @ // The result must be the element at index n
     @ ensures \result == data[n];
     @*/
    public /*@pure@*/ int get(int n) {
        return data[n];
    }

    /**
     * Add {n} in the set. Returns the index where {n} was inserted.
     */
    /*@
     @ // there must be at least one space left
     @ requires size < data.length;
     @ // no modifications before the index of the added element
     @ ensures (\forall int i; 0 <= i && i < \result; data[i] == \old(data[i]));
     @ // if 'n' was not in the set, all the elements after the insertion
     @ // are shifted of one index
     @ ensures !\old(contains(n)) ==> (\forall int i; \result < i && i < \old(size); data[i+1] == \old(data[i]));
     @ // n is in the array at the index given as a result
     @ ensures n == data[\result];
     @ // if 'n' was not in the set, the size must be incremented
     @ ensures !\old(contains(n)) ==> size == \old(size) + 1;
     @ // the index of the new element must be inbounds
     @ ensures 0 <= \result && \result < size;
     @*/
    private int enqueue(int n) {
        int i = indexOf(n);

        if (! contains(n)) {
            int j = size;
            while (j > i) {
                data[j] = data[j-1];
                j = j - 1;
            }
            data[i] = n;
            size = size + 1;
        }
        return i;
    }

    /**
     * Remove and return highest (i.e. last) element in the queue.
     */
    /*@
     @ // the size should be decremented
     @ modifies size;
     @ // there must be at least one element
     @ requires 1 <= size;
     @ // the result should be the one at the previous-last index
     @ ensures \result == \old(data[size-1]);
     @ // the size must be decremented of 1
     @ ensures size == \old(size) - 1;
     @*/
    public int dequeue() {
        size = size - 1;
        return data[size];
    }

    /**
     * Returns the index of the first element greater or equal to {n} in the queue.
     * Returns the size of the queue if all elements are smaller than {n}.
     */
    /*@
     @ // The result will be whether in the bounds of the elements, whether the size
     @ ensures 0 <= \result && \result <= size;
     @ // The result is 'size' OR the result is inside the bounds which means that
     @ // an element greater or equals to 'n' exists in the array
     @ ensures (\result == size) || (0 <= \result && \result < size <==> data[\result] >= n);
     @ // all elements at a previous index than the given result are lower than 'n'
     @ ensures (\forall int i; 0 <= i & i < \result; data[i] < n);
     @*/
    public /*@pure@*/ int indexOf(int n) {
        int i = 0;
        while (i < size && data[i] < n) {
            i = i + 1;
        }
        return i;
    }

    /**
     * Returns {true} iff {n} is in the queue.
     */
    /*@
     @ // return true iff n is in the queue
     @ ensures \result <==> (indexOf(n) < size) && (data[indexOf(n)] == n);
     @*/
    public /*@pure@*/ boolean contains(int n) {
        int i = indexOf(n);
        return (i < size && data[i] == n);
    }
}
