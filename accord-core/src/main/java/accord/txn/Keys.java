package accord.txn;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import accord.api.Key;
import accord.api.KeyRange;
import accord.topology.KeyRanges;

@SuppressWarnings("rawtypes")
public class Keys implements Iterable<Key>
{
    public static final Keys EMPTY = new Keys(new Key[0]);

    final Key[] keys;

    public Keys(SortedSet<? extends Key> keys)
    {
        this.keys = keys.toArray(Key[]::new);
    }

    public Keys(Collection<? extends Key> keys)
    {
        this.keys = keys.toArray(Key[]::new);
        Arrays.sort(this.keys);
    }

    public Keys(Key[] keys)
    {
        this.keys = keys;
        Arrays.sort(keys);
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Keys keys1 = (Keys) o;
        return Arrays.equals(keys, keys1.keys);
    }

    @Override
    public int hashCode()
    {
        return Arrays.hashCode(keys);
    }

    public int indexOf(Key key)
    {
        return Arrays.binarySearch(keys, key);
    }

    public Key get(int indexOf)
    {
        return keys[indexOf];
    }

    public Keys select(int[] indexes)
    {
        Key[] selection = new Key[indexes.length];
        for (int i = 0 ; i < indexes.length ; ++i)
            selection[i] = keys[indexes[i]];
        return new Keys(selection);
    }

    public boolean isEmpty()
    {
        return keys.length == 0;
    }

    public int size()
    {
        return keys.length;
    }

    public int search(int lowerBound, int upperBound, Object key, Comparator<Object> comparator)
    {
        return Arrays.binarySearch(keys, lowerBound, upperBound, key, comparator);
    }

    public int ceilIndex(int lowerBound, int upperBound, Key key)
    {
        int i = Arrays.binarySearch(keys, lowerBound, upperBound, key);
        if (i < 0) i = -1 - i;
        return i;
    }

    public int ceilIndex(Key key)
    {
        return ceilIndex(0, keys.length, key);
    }

    public Stream<Key> stream()
    {
        return Stream.of(keys);
    }

    @Override
    public Iterator<Key> iterator()
    {
        return new Iterator<>()
        {
            int i = 0;
            @Override
            public boolean hasNext()
            {
                return i < keys.length;
            }

            @Override
            public Key next()
            {
                return keys[i++];
            }
        };
    }

    @Override
    public String toString()
    {
        return stream().map(Object::toString).collect(Collectors.joining(",", "[", "]"));
    }

    public static Keys of(Key k0, Key... kn)
    {
        Key[] keys = new Key[kn.length + 1];
        keys[0] = k0;
        for (int i=0; i<kn.length; i++)
            keys[i + 1] = kn[i];

        return new Keys(keys);
    }

    public Keys intersection(KeyRanges ranges)
    {
        Key[] result = null;
        int resultSize = 0;

        int keyLB = 0;
        int keyHB = size();
        int rangeLB = 0;
        int rangeHB = ranges.rangeIndexForKey(keys[keyHB-1]);
        rangeHB = rangeHB < 0 ? -1 - rangeHB : rangeHB + 1;

        for (;rangeLB<rangeHB && keyLB<keyHB;)
        {
            Key key = keys[keyLB];
            rangeLB = ranges.rangeIndexForKey(rangeLB, ranges.size(), key);

            if (rangeLB < 0)
            {
                rangeLB = -1 -rangeLB;
                if (rangeLB >= rangeHB)
                    break;
                keyLB = ranges.get(rangeLB).lowKeyIndex(this, keyLB, keyHB);
            }
            else
            {
                if (result == null)
                    result = new Key[keyHB - keyLB];
                KeyRange<?> range = ranges.get(rangeLB);
                int highKey = range.higherKeyIndex(this, keyLB, keyHB);
                int size = highKey - keyLB;
                System.arraycopy(keys, keyLB, result, resultSize, size);
                keyLB = highKey;
                resultSize += size;
                rangeLB++;
            }

            if (keyLB < 0)
                keyLB = -1 - keyLB;
        }

        if (result != null && resultSize < result.length)
            result = Arrays.copyOf(result, resultSize);

        return result != null ? new Keys(result) : EMPTY;
    }


}