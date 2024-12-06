public class ComplexTest {
    static int staticField = 10;

    public static void main(String[] args) {
        ComplexTest.example();
    }

    public static void example() {
        // Integer operations
        int a = 42; // iload, istore
        int b = 5;
        int sum = a + b; // iadd
        int diff = a - b; // isub
        int product = a * b; // imul
        int quotient = a / b; // idiv
        int remainder = a % b; // irem

        // Floating-point operations
        float x = 3.5f; // fload, fstore
        float y = 1.5f;
        float result = x / y; // fdiv

        // Double operations
        double d = 3.14; // dload, dstore
        double doubleResult = d * 2; // dmul

        // Long operations
        long bigNum = 1_000_000_000L; // lload, lstore
        long bigResult = bigNum + 42; // ladd

        // Array manipulations
        int[] numbers = {1, 2, 3}; // iconst, anewarray, aastore, aload
        int first = numbers[0]; // iaload
        numbers[1] = 42; // iastore

        // Logical operations
        boolean check = a > b; // if_icmpgt

        // Static field access
        int staticValue = staticField; // getstatic

        // Object instantiation and method calls
        String text = new String("Hello"); // new, invokespecial
        System.out.println(text); // invokevirtual
        int length = text.length(); // invokevirtual

        // Casting
        double castedValue = (double) sum; // i2d

        // Loops and branching
        for (int i = 0; i < numbers.length; i++) { // if_icmplt, goto
            System.out.println(numbers[i]); // invokevirtual
        }

        if (check) { // ifne
            System.out.println("a is greater than b"); // ldc, invokevirtual
        } else {
            System.out.println("b is greater or equal to a");
        }

        // Method invocation
        int squareResult = square(a); // invokestatic

        // Exceptions
        try {
            int badResult = numbers[5]; // Throws ArrayIndexOutOfBoundsException
        } catch (Exception e) {
            System.out.println("Caught exception: " + e.getMessage()); // invokevirtual
        }
    }

    public static int square(int n) {
        return n * n; // imul
    }
}