/*
** Copyright (C) 2008 José Vander Meulen <jose.vandermeulen@uclouvain.be>, 
**                    Charles Pecheur <charles.pecheur@uclouvain.be>
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/

public class PatternMatching {

    /**
     * Returns true iff p occurs as a substring in t starting at index k.
     */
    /*@@
     @ requires p != null;
     @ requires t != null;
     @ requires 0 <= k;
     @ ensures \result <==> ((k + p.length <= t.length) && (\forall int i; 0 <= i && i < p.length ; p[i] == t[i+k]));
     @*/
    private static /*@ pure @*/ boolean matches(int[] p, int[] t,  int k) {
        boolean result;
        if (k + p.length > t.length) {
            result = false;
        } else {
            //@ assert k + p.length <= t.length;
            int i = 0;
            boolean match = true;
            //@ loop_invariant 0 <= i && i <= p.length && k + i <= t.length;
            //@ loop_invariant match <==> (\forall int a ; 0 <= a && a < i ; p[a]==t[a+k]); 
            //@ decreasing p.length - i ;
            while (i != p.length && match) {
                match = p[i] == t[k + i];
                i = i + 1;
            }
            result = match;
        }
        return result;
    }

    /**
     * 	Returns the smallest index i such that p is a substring of
	 * t starting at i.  Returns a negative number if p is not
	 * a substring of t.
     */
    /*@@
     @ requires p != null;
     @ requires t != null;
     @ ensures \result >= 0 <==> (\exists int k; 0 <= k && k <= t.length - p.length; matches(p, t, k));
     @*/
    public static int find(int[] p, int[] t) {
        int i = 0;
        //@ loop_invariant 0 <= i;
        //@ loop_invariant (\forall int k; 0 <= k && k < i; !matches(p,t,k));
        //@ decreasing t.length - p.length - i;
        while (i <= t.length - p.length) {
            if (matches(p, t, i)) {
                return i;
            }
            i = i + 1;
        }
        return -1;
    }    

    /**
     * Returns the smallest index i after n such that p is a
     * substring of t starting at i. Returns a negative number if
     * p is not a substring of t.
     */
    /*@@
     @ requires p != null;
     @ requires t != null;
     @ requires n >= 0;
     @ ensures \result >= 0 <==> (\exists int k; n <= k && k <= t.length - p.length; matches(p, t, k));
     @*/
    public static /*@ pure @*/ int find(int[] p, int[] t, int n) {
        int i = n;
        //@ loop_invariant n <= i;
        //@ loop_invariant (\forall int k; n <= k && k < i ; !matches(p, t, k));
        while (i <= t.length - p.length) {
            if (matches(p, t, i)) {
                return i;
            }
            i = i + 1;
        }
        return -1;
    }
    
    public static /*@ pure @*/ int findLast(int[] p, int[] t) {
    }
}
