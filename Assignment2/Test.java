/*
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
 * A test class for Queue.
 */

public class Test {

    //@ requires n > 0;
    public static void test(int n) {
        Queue q = new Queue(n);
        //@ assert q.size() == 0;
        for (int i = 0; i < n; i++) {
            int elem = i % 3;   // 0, 1, 2, 0, 1, 2, ...
            int pos = q.enqueue(elem);
            //@ assert q.get(pos) == elem;
        }
        //@ assert q.size() == n;
        q.noDup();
        //@ assume q.size() >= 2;
        int elem1 = q.dequeue();
        int elem2 = q.dequeue();
        //@ assert elem1 != elem2;
    }

}