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
**
** Specifications in JML by Florian THUIN (SINF21MS/G) and Symeon MALENGREAU (SINF22MS/G)
** LINGI2224 - Programming methods 2015-2016
** Assignment 1, March 07, 2016
*/

public class PatternMatching {

    /**
     * Returns true iff p occurs as a substring in t starting at index k.
     */

    /*@@
     @ // No table can be null because the method needs the length attribute.
     @ // The two next lines are to avoid null dereferences.
     @ requires p != null;
     @ requires t != null;
     @ // k should be an index of the table, k has to be non-negative.
     @ requires 0 <= k;
     @ // Returns true iff:
     @ // 1) k + the pattern length isn't greater than the table length
     @ // AND
     @ // 2) each element at index i from 0 to k in the pattern matches each element at index i to i+k in the table
     @ ensures \result <==> ((k + p.length <= t.length) && (\forall int i; 0 <= i && i < p.length ; p[i] == t[i+k]));
     @*/
    private static /*@ pure @*/ boolean matches(int[] p, int[] t,  int k) {
        boolean result;
        if (k + p.length > t.length) {
            result = false;
        } else {
            int i = 0;
            boolean match = true;
            // From precondition we know k >= 0,
            // In this part of the condition, we know k + p.length <= t.length

            // 'i' will iterate over 'p' as follow:
            //
            // | 0 |         ...          | p.length
            // +---+----------------------+
            // | i |                      |
            // |---+--+---+---+--+--+--+--+
            // |   |  |   |   |  |  |  |  |
            // +---+--+---+---+--+--+--+--+
            //
            // | 0 |         ...          | p.length
            // +---+------+---+-----------+
            // |   |      | i |           |
            // |---+--+---+---+--+--+--+--+
            // |   |  |   |   |  |  |  |  |
            // +---+--+---+---+--+--+--+--+
            // Such that we need 0 <= i < p.length during the iteration
            // over 'p', the case where i==p.length (at the latest, if match)
            // that would be an out-of-bound case is handled by the
            // end-condition of the while-loop (i==p.length will exit
            // the loop without ever be an index of 'p' and will never
            // enter the loop).
            //
            // 'k+i' will iterate over 't' as follow:
            // | k |          ...         | t.length
            // +---+----------------------+
            // | i |                      |
            // +---+---+---+---+---+---+--+
            // |   |                      |
            // +---+---+---+---+---+---+--+
            //
            // | k |          ...         | t.length
            // +---+-------+---+----------+
            // |   |       | i |          |
            // +---+---+---+---+---+---+--+
            // |   |                      |
            // +---+---+---+---+---+---+--+
            // Such that we need 0 <= k + i < t.length during the
            // iteration over 't', the case where k+i==t.length (at the
            // latest, if match) that would be an out-ouf-bound case is
            // handled by the end-condition of the while-loop AND by the
            // 'if' condition (this part is the 'else' of an if..then..else
            // construction)
            //
            //@ loop_invariant 0 <= i && i <= p.length && k + i <= t.length;
            // Match must be true iff the already-visited-pattern from
            // 0 to i exclusive matches the already-visited-table from k
            // to i+k exclusive.
            //@ loop_invariant match <==> (\forall int a ; 0 <= a && a < i ; p[a]==t[a+k]);

            // As 'i' is the index for 'p' and it is increasing at
            // each iteration and 'p' isn't modified (this is a pure
            // method), p.length - i is the variant of this loop.
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
     @ // No table can be null because the method needs the length attribute.
     @ // The two next lines are to avoid null dereferences.
     @ requires p != null;
     @ requires t != null;
     @ // This method will return a non-negative number iff
     @ // there exists a 'k' from 0 to t.length - p.length such that
     @ // matches(p,t,k) returns true (i.e. 'p' is a substring of 't' starting
     @ // at index 'k').
     @ ensures \result >= 0 <==> (\exists int k; 0 <= k && k <= t.length - p.length; matches(p, t, k));
     @ // A positive result has to be the smallest index:
     @ ensures \result >= 0 ==> (\forall int a; 0 <= a && a < \result; !matches(p,t,a));
     @ // A positive result has to be inside the bounds
     @ ensures \result >= 0 ==>  \result <= t.length - p.length;
     @ // A positive result has to be the exact index where p matches t
     @ ensures \result >= 0 ==> matches(p,t,\result);
     @*/
    public static /*@ pure @*/ int find(int[] p, int[] t) {
        int i = 0;
        // 'i' is an index of arrays, must be non-negative
        //@ loop_invariant 0 <= i;
        //
        // No substring with the pattern 'p' in 't' starts from an index
        // between 0 and 'i' exclusive.
        //@ loop_invariant (\forall int k; 0 <= k && k < i; !matches(p,t,k));
        //
        // As the loop iterates, 'i' is increasing. As the method is
        // pure, the length of 't' or 'p' doesn't change, such that
        // this is a possible variant:
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
     @ // No table can be null because the method needs the length attribute.
     @ // The two next lines are to avoid null dereferences.
     @ requires p != null;
     @ requires t != null;
     @ // n should be an index of the table, n has to be non-negative.
     @ requires n >= 0;
     @ // Result must be positive iff
     @ // there is a substring matching 'p' in a part of 't' starting at index 'n'.
     @ ensures \result >= 0 <==> (\exists int k; n <= k && k <= t.length - p.length; matches(p, t, k));
     @ // The result has to be the first one that matches after 'n'
     @ ensures \result >= 0 ==> (\forall int a; n <= a && a < \result; !matches(p,t,a));
     @ // A positive index result can only be between 'n' and the last possible matching index
     @ ensures \result >= 0 <==> (n <= \result && \result <= t.length - p.length);
     @ // The result must be an index where p matches t
     @ ensures \result >= 0 ==> matches(p,t,\result);
     @*/
    public static /*@ pure @*/ int find(int[] p, int[] t, int n) {
        int i = n;
        // 'i' must be positive (as n>=0 in the pre) because it is a
        // precondition of matches, and 'i' is an index
        // greater than or equals to n:
        //@ loop_invariant n <= i;

        // No substring with the pattern 'p' in 't' starts from an index
        // between 'n' and 'i' exclusive.
        //@ loop_invariant (\forall int k; n <= k && k < i ; !matches(p, t, k));

        // As the loop iterates, 'i' is increasing. As the method is
        // pure, the length of 't' or 'p' doesn't change, such that
        // this is a possible variant:
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
     * Returns the highest index i after such that p is a substring
     * of t starting at i. Returns a negative number if p
     * is not a substring of t.
     */
    /*@@
     @ // No table can be null because the method needs the length attribute.
     @ // The two next lines are to avoid null dereferences.
     @ requires p != null;
     @ requires t != null;
     @ // This method will return a non-negative number iff
     @ // there exists a 'k' from 0 to t.length - p.length such that
     @ // matches(p,t,k) returns true (i.e. 'p' is a substring of 't' starting
     @ // at index 'k').
     @ ensures \result >= 0 <==> (\exists int k; 0 <= k && k <= t.length - p.length ; matches(p, t, k));
     @ // As a non-negative value as a result isn't sufficient, we also need
     @ // this non-negative value to be the last one inside the bound of the
     @ // table. That means there are no substring matching 'p' at any
     @ // greater index of 't' than the given result.
     @ ensures \result >= 0 ==> (\forall int j; \result < j && j <= t.length - p.length ; !matches(p, t, j));
     @ // The result must be inside the bounds:
     @ ensures \result >= 0 ==> \result <= t.length - p.length;
     @ // The resulting index must be exactly the one where the pattern matches in the table
     @ ensures \result >= 0 ==> matches(p,t,\result);
     @*/
    public static /*@ pure @*/ int findLast(int[] p, int[] t) {
        int i = 0;
        int k = -1;
        // 'i' is an array index, it has to be positive (it is a
        // precondition of matches)
        //@ loop_invariant 0 <= i;
        // 'k' is the last index where a substring matching 'p'
        // has been found in 't':
        //@ loop_invariant (\forall int a; k < a && a < i; !matches(p, t, a));
        // If 'k' is non-negative, it means that 'p' is a substring
        // of 't' starting at 'k':
        //@ loop_invariant k >= 0 ==> matches(p,t,k);
        // As the loop iterates, 'i' is increasing. As the method is
        // pure, the length of 't' or 'p' doesn't change, such that
        // this is a possible variant:
        //@ decreasing t.length - p.length - i;
        while (i <= t.length - p.length) {
            if (matches(p, t, i)) {
                k = i;
            }
            i = i + 1;
        }
        return k;
    }
}
