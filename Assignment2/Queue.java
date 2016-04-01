/*
 ** Copyright (C) 2008 Jos� Vander Meulen <jose.vandermeulen@uclouvain.be>
 ** Copyright (C) 2010 Charles Pecheur <charles.pecheur@uclouvain.be>
 **
 ** This program is free software; you can redistribute it and/or modify
 ** it under the terms of the GNU General Public License as published by
 ** the Free Software Foundation; either version 2 of the License, or
 ** (at your option) any later version.
 **
 ** This program is distributed in the hope that it will be useful,
 ** but WITHOUT ANY WARRANTY; without even the implied warranty of
 ** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. �See the
 ** GNU General Public License for more details.
 **
 ** You should have received a copy of the GNU General Public License
 ** along with this program; if not, write to the Free Software
 ** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 ** Specifications in JML by Florian THUIN (SINF21MS/G) and Symeon MALENGREAU (SINF22MS/G)
 ** LINGI2224 - Programming methods 2015-2016
 ** Assignment 2, April 01, 2016
 */

/**
 * A bounded priority queue (of integers), implemented as an ordered array where elements
 * are kept sorted.
 */
public class Queue {

    /* * * * * *
     * FIELDS  *
     * * * * * */
    private /*@spec_public@*/ int[] data;    // the elements of the queue
    private /*@spec_public@*/ int size;      // the number of elements in the queue

    /* * * * * * * * * * *
     * Class invariants  *
     * * * * * * * * * * */
    // data must never be null
    //@ invariant data != null;
    // the size should be non-negative and not greater than data.length
    //@ invariant 0 <= size && size <= data.length;
    // the array must be sorted in ascending order
    //@ invariant (\forall int i, j; 0 <= i && i < j && j < size ; data[i] <= data[j] );
    // The owner of data is this object
    //@ invariant data.owner == this;

    /* * * * * *
     * Methods *
     * * * * * */

    /**
     * Return an empty stack with a capacity of max elements (max >= 0).
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
    public Queue(int max) {
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
     * Add {n} in the queue.  Returns the index where {n} was inserted.
     */
    /*@
     @ // size must change (adding an element increments size)
     @ modifies size;
     @ // the element at indexOf(n) will be n and the elements after are shifted
     @ modifies data[indexOf(n)..size];
     @ // there must be at least one space left
     @ requires size < data.length;
     @ // no modifications before the index of the added element
     @ ensures (\forall int i; 0 <= i && i < \result; data[i] == \old(data[i]));
     @ // all elements in the new array after the added elements are the same,
     @ // shifted of one index
     @ ensures (\forall int i; \result < i && i < \old(size) ; data[i+1] == \old(data[i]));
     @ // n is in the array at the index given as a result
     @ ensures n == data[\result];
     @ // the size was incremented
     @ ensures size == \old(size) + 1;
     @ // the result will be in the bounds of the size
     @ ensures 0 <= \result && \result < size;
     @*/
    public int enqueue(int n) {
        int i = indexOf(n);

        // shift elements one index up, from size-1 down to i.
        int j = size;
        // TODO REMOVE @ loop_invariant i <= j && j <= size;
        //@ decreases j - i;
        while (j > i) {
            data[j] = data[j-1];
            j = j - 1;
        }

        data[i] = n;
        size = size + 1;
        return i;
    }


    /**
     * Remove and return highest (i.e. last) element in the queue.
     */
    /*@
     @ // the size should be decremented
     @ modifies size;
     @ // TODO REMOVE modifies data[size-1];
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
        //@ loop_invariant 0 <= i && i <= size;
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

    /*@
     @ // a newArray must be of a positive length, not null, of a given size,
     @ // initializes elements at 0 and the given variable must be new.
     @ requires 0 <= n;
     @ ensures \result != null;
     @ ensures \result.length == n;
     @ ensures (\forall int i; 0 <= i && i < n; \result[i]==0);
     @ ensures \fresh(\result);
     @ private static pure model int[] newArray(int n);
     @*/
    /**
     * Removes duplicates in the list.
     */
    /*@
     @ private static ghost int[] neededIndex;
     @ //modifies data[0..size];
     @ // modifies size;
     @ // modifies neededIndex;
     @ TODO REMOVE //////////////////////////////////////////////////
     @ TODO REMOVE //ensures (\forall int k, l ;
     @ TODO REMOVE //         0 <= k && k < size &&
     @ TODO REMOVE //         0 <= l && l < size &&
     @ TODO REMOVE //         k != l ;
     @ TODO REMOVE //         data[k] != data[l]);
     @ TODO REMOVE //ensures (\forall int k ; 0 <= k && k < size ;
     @ TODO REMOVE //         (\exists int l ; 0 <= l && l <= \old(size) ;
     @ TODO REMOVE //          data[k] == \old(data[l])));
     @ TODO REMOVE //ensures (\forall int k ; 0 <= k && k < \old(size) ;
     @ TODO REMOVE //        data[neededIndex[k]] == \old(data[k]));
     @ TODO REMOVE ////////////////////////////////////////////////////
     @ // Every element in the new array appears only once
     @ ensures (\forall int i, j; 0 <= i && i < j && j < size; data[i] != data[j]);
     @ // Every element in the new array was in the old array
     @ ensures (\forall int i; 0 <= i && i < size ; (\exists int j; 0 <= j && j < \old(size); data[i]==\old(data[j])));
     @ // Every element in the old array is in the new array
     @ ensures (\forall int k; 0 <= k && k < \old(size); data[neededIndex[k]] == \old(data[k]));
     @ //ensures (\forall int i; 0 <= i && i < neededIndex.length; (\exists int j; 0 <= j && j < size; neededIndex[i]==data[j]));
     @ //ensures (\forall int i; 0 <= i && i < \old(size) ; (\exists int j; 0 <= j && j < size; data[j]==\old(data)[i]));
     @ // ensures (\forall int a; 0 <= a && a < \old(size); contains(\old(data[a])));
     @*/
    public void noDup() {
        // whole new array of length 'size'
        //@ set neededIndex = newArray(size);
        //@ assert neededIndex.length == size;

        int i = 0; // current element in the old list
        int j = 0; // next spot to fill in the new list

        // TODO : Vérifier la nécessité de l'invariant
        //@ loop_invariant (\forall int a, b; 0 <= a && a < b && b < j; data[a] != data[b]);
        //@ loop_invariant 0 <= i;
        //@ decreases size - i;
        while (i < size) {
            data[j] = data[i];
            //@ set neededIndex[i] = j;
            i = i + 1;
            //@ decreases size - i;
            while (i < size && data[i] == data[j]) {
                //@ set neededIndex[i] = j;
                i = i + 1;
            }
            j = j + 1;
        }
        size = j;
    }

}
