public class Set {
    public int[] data;
    private int size;

    public Set(int max) {
        this.data = new int[max];
        this.size = 0;
    }

    public int size() {
        return size;
    }
    public int enqueue(int n) {
        int i = indexOf(n);
        int j = size;
        while (j > i) {
            data[j] = data[j-1];
            j = j - 1;
        }
        data[i] = n;
        size = size + 1;
        return i;
    }
    public int dequeue() {
        size = size - 1;
        return data[size];
    }
    public int indexOf(int n) {
        int i = 0;
        while (i < size && data[i] < n) {
            i = i + 1;
        }
        return i;
    }

    public boolean contains(int n) {
        int i = indexOf(n);
        return (i < size && data[i] == n);
    }
}
