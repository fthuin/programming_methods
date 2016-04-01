public class Set {

    /* * * * * *
     * Fields  *
     * * * * * */
    private /*@spec_public@*/ int[] data;
    private /*@spec_public@*/int size;

    /* * * * * * * * * * *
     * Class invariants  *
     * * * * * * * * * * */

    //@ invariant data != null;
    //@ invariant 0 <= size && size <= data.length;
    //@ invariant (\forall int i, j; 0 <= i && i < j && j < size; data[i] < data[j]);
    //@ invariant data.owner == this;

    /*@
     @ modifies data;
     @ modifies size;
     @ requires 0 <= max;
     @ ensures size == 0;
     @ ensures data.length == max;
     @*/
    public Set(int max) {
        this.data = new int[max];
        //@ set data.owner = this; 
        this.size = 0;
    }

    /*@
     @ ensures \result == size;
     @*/
    public /*@pure@*/ int size() {
        return size;
    }

    /*@
     @ requires 0 <= n && n < size;
     @ ensures \result == data[n];
     @*/
    public int get(int n) {
        return data[n];
    }

    /*@
     @ requires size < data.length;
     @ ensures (\forall int i; 0 <= i && i < \result; data[i] == \old(data[i]));
     @ ensures !\old(contains(n)) ==> (\forall int i; \result < i && i < \old(size); data[i+1] == \old(data[i]));
     @ ensures n == data[\result];
     @ ensures !\old(contains(n)) ==> size == \old(size) + 1;
     @ ensures 0 <= \result && \result < size;
     @*/
    private int enqueue(int n) {
        int i = indexOf(n);

        if (! contains(n)) {
            int j = size;
            //@ loop_invariant i <= j && j <= size;
            //@ decreases j - i;
            while (j > i) {
                data[j] = data[j-1];
                j = j - 1;
            }
            data[i] = n;
            size = size + 1;
        }
        return i;
    }

    /*@
     @ modifies size;
     @ modifies data[size-1];
     @ requires 1 <= size;
     @ ensures \result == \old(data[size-1]);
     @ ensures size == \old(size) - 1;
     @*/
    public int dequeue() {
        size = size - 1;
        return data[size];
    }

    /*@
     @ ensures 0 <= \result && \result <= size;
     @ ensures (\result == size) || (0 <= \result && \result < size <==> data[\result] >= n);
     @ ensures (\forall int i; 0 <= i && i < \result; data[i] < n);
     @*/
    public /*@pure@*/ int indexOf(int n) {
        int i = 0;
        while (i < size && data[i] < n) {
            i = i + 1;
        }
        return i;
    }

    /*@
     @ ensures \result <==> (indexOf(n) < size) && (data[indexOf(n)] == n);
     @*/
    public /*@pure@*/ boolean contains(int n) {
        int i = indexOf(n);
        return (i < size && data[i] == n);
    }
}
