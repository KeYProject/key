public class Textblock {

    // Expected One large string w/o newlines
    String text = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.";

    // Expected: strip indentation and new lines. Four spaces before <body>.
    String html = "<html>\n    <body>\n        <p>Hello, world</p>\n    </body>\n</html>\n";

    // Expected: String with newlines and escaped quotes.
    String query = "SELECT \"EMP_ID\", \"LAST_NAME\" FROM \"EMPLOYEE_TB\"\nWHERE \"CITY\" = 'INDIANAPOLIS'\nORDER BY \"EMP_ID\", \"LAST_NAME\";\n";

    Object obj = ("function hello() {\n    print('\"Hello, world\"');\n}") + "hello();\n";

    //expected "line 1\nlines 2\nline 3\n"
    String simple = "line 1\nline 2\nline 3\n";

    //Expected: newlines and escaped quotes
    String code = "String text = \"\"\"\n    A text block inside a text block\n\"\"\";\n";

    String abc = ("     1 \"\n     2 \"\"\n     3 \"\"\"\n     4 \"\"\"\"\n     5 \"\"\"\"\"\n     6 \"\"\"\"\"\"\n     7 \"\"\"\"\"\"\"\n     8 \"\"\"\"\"\"\"\"\n     9 \"\"\"\"\"\"\"\"\"\n    10 \"\"\"\"\"\"\"\"\"\"\n    11 \"\"\"\"\"\"\"\"\"\"\"\n    12 \"\"\"\"\"\"\"\"\"\"\"\"\n");

    String text = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.";

    String colors = "red   \ngreen \nblue  \n";

    // attention trailing whitespaces!
    String colors = "red\ngreen\nblue\n";
}
