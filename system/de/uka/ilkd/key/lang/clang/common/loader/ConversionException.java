package de.uka.ilkd.key.lang.clang.common.loader;

public class ConversionException extends Exception {
        public ConversionException(String message, LoadingContext context) {
                this(message, context, null);
        }
        
        public ConversionException(String message, LoadingContext context, Throwable cause) {
                super(buildMessage(message, context), cause);
        }
        
        
        private static String buildMessage(String message, LoadingContext context) {
                StringBuffer buffer = new StringBuffer();
                buffer.append(message);
                if (context.getPosition() != null)
                        buffer.append("\nPosition: "+ context.getPosition());
                if (context.getFileName() != null)
                        buffer.append("\nFilename: " + context.getFileName());
                if (context.getSource() != null)
                        buffer.append("\nSource:\n" + context.getSource());
                return buffer.toString();
        }
}
