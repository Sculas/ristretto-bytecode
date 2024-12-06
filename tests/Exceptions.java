public class Exceptions {
    public void example() {
        try {
            throw new NullPointerException("Something went wrong!"); // athrow
        } catch (NullPointerException e) {
            System.out.println("Caught exception: " + e.getMessage()); // invokevirtual
        } catch (ArrayIndexOutOfBoundsException e) {
            System.out.println("Caught exception: " + e.getMessage()); // invokevirtual
        }
    }
}