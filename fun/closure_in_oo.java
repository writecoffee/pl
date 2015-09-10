public class closure_in_oo
{
    static interface Func<A, B>
    {
        B apply(A x);
    }

    static interface Pred<A>
    {
        boolean apply(A x);
    }

    static class NilList<T> extends List<T>
    {
        NilList()
        {
            super(null, null);
        }
    }

    static class List<T>
    {
        T       head;
        List<T> tail;

        List(T x, List<T> xs)
        {
            head = x;
            tail = xs;
        }

        public boolean isEmpty()
        {
            return head == null;
        }

        public static <A, B> List<B> map(Func<A, B> f, List<A> xs)
        {
            if (xs instanceof NilList) {
                return new NilList<>();
            }

            return new List<B>(f.apply(xs.head), map(f, xs.tail));
        }

        public static <A> List<A> filter(Pred<A> f, List<A> xs)
        {
            if (xs instanceof NilList) {
                return new NilList<>();
            }

            if (f.apply(xs.head)) {
                return new List<>(xs.head, filter(f, xs.tail));
            }

            return filter(f, xs.tail);
        }

        public static <A> int length(List<A> xs)
        {
            int result = 0;

            while (!xs.isEmpty()) {
                result++;
                xs = xs.tail;
            }

            return result;
        }
    }

    static class Client
    {
        public static List<Integer> doubleAll(List<Integer> xs)
        {
            return List.map(new Func<Integer, Integer>()
            {
                @Override
                public Integer apply(Integer x)
                {
                    return x * 2;
                }
            }, xs);
        }

        public static int countNs(List<Integer> xs, final int n)
        {
            return List.length(List.filter(new Pred<Integer>()
            {
                @Override
                public boolean apply(Integer x)
                {
                    return x == n;
                }
            }, xs));
        }
    }
}
