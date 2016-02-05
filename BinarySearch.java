public class BinarySearch {
  public static int search(int[] a, int key) {
    return search(a, key, 0, a.length);
  }
  /**
   * Binary search in a subrange of a sorted array.
   * @pre (a) is a sorted array of integers and
   *      (low) and (high-1) are indices in (a)
   * @post returns the index of the first element larger or
   *       equal to (key) between (low) and (high-1)
   *       or (high) if not found
   */
  public static int search(int[] a, int key, int low, int high) {
    if (low >= high) return low;
    else if (a[low] >= key) return low;
    else if (a[high-1] < key) return high;
    else {
      int mid = (low + high) / 2;
      if (a[mid] >= key) return search(a,key,low,mid);
      else return search(a,key,mid,high);
    }
  }
}
