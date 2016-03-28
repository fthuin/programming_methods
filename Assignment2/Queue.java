/*
 ** Copyright (C) 2008 José Vander Meulen <jose.vandermeulen@uclouvain.be>
 ** Copyright (C) 2010 Charles Pecheur <charles.pecheur@uclouvain.be>
 **
 ** This program is free software; you can redistribute it and/or modify
 ** it under the terms of the GNU General Public License as published by
 ** the Free Software Foundation; either version 2 of the License, or
 ** (at your option) any later version.
 **
 ** This program is distributed in the hope that it will be useful,
 ** but WITHOUT ANY WARRANTY; without even the implied warranty of
 ** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 ** GNU General Public License for more details.
 **
 ** You should have received a copy of the GNU General Public License
 ** along with this program; if not, write to the Free Software
 ** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

/**
 * A bounded priority queue (of integers), implemented as an ordered array where elements
 * are kept sorted.
 */
public class Queue {

    private  int[] data;    // the elements of the queue
    private  int size;      // the number of elements in the queue

    /**
     * Return an empty stack with a capacity of max elements (max >= 0).
     */
    public Queue(int max) {
        this.data = new int[max];
        this.size = 0;
    }

    /**
     * Return the size of the queue.
     */
    public int size() {
        return size;
    }

    /**
     * Return element at index {n}.
     */
    public int get(int n) {
        return data[n];
    }

    /**
     * Add {n} in the queue.  Returns the index where {n} was inserted.
     */
    public int enqueue(int n) {
        int i = indexOf(n);

        // shift elements one index up, from size-1 down to i.
        int j = size;
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
    public int dequeue() {
        size = size - 1;
        return data[size];
    }

    /**
     * Returns the index of the first element greater or equal to {n} in the queue.  
     * Returns the size of the queue if all elements are smaller than {n}.
     */
    public int indexOf(int n) {
        int i = 0;
        while (i < size && data[i] < n) {
            i = i + 1;
        }
        return i;
    }

    /**
     * Returns {true} iff {n} is in the queue.  
     */
    public boolean contains(int n) {
        int i = indexOf(n);
        return (i < size && data[i] == n);
    }

    /**
     * Removes duplicates in the list.
     */
    public void noDup() {

        int i = 0; // current element in the old list
        int j = 0; // next spot to fill in the new list

        while (i < size) {
            data[j] = data[i];
            i = i + 1;
            while (i < size && data[i] == data[j]) {
                i = i + 1;
            }
            j = j + 1;
        }
        size = j;
    }

}