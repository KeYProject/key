package de.uka.ilkd.key.lang.clang.common.loader;

/**
 * Represents a state in program loading.
 * 
 * @author oleg.myrk@gmail.com
 */
public class LoadingContext {
        private String fileName;
        private String position;
        private String source;
        
        public LoadingContext(String fileName, String position, String source) {
                super();
                this.fileName = fileName;
                this.position = position;
                this.source = source;
        }
        
        public LoadingContext(String fileName, int[] position, String source) {
                super();
                this.fileName = fileName;
                this.position = formatPosition(position);
                this.source = source;
        }
        
        private static String formatPosition(int[] position) {
                return "(" + position[0] + "," + position[1] + ")";                        
        }

        public String getFileName() {
                return fileName;
        }

        public String getPosition() {
                return position;
        }

        public String getSource() {
                return source;
        }
}