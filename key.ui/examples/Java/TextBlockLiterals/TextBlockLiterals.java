public final class TextBlockLiterals {
    /*@ ensures true; requires true; */
    public void m()  {
        String textBlock = """
                line 1    
                line 2    
                line 3
                """;

        String oldFashionedLiteral = "line 1\nline 2\nline 3\n";

        assert(textBlock.equals(oldFashionedLiteral));
    }
}