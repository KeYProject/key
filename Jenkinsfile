pipeline {
    agent {
        docker {
            image 'wadoon/key-test-docker:jdk11'
        }
    }

    environment {
        GRADLE_OPTS = '-Dorg.gradle.daemon=false'
    }

    stages {
        stage('Clean') {
            steps{
                sh 'javac -version'
                sh 'key/scripts/jenkins/startupClean.sh'
            }
        }

        stage('Compile') {
            steps { 
                sh 'cd key && ./gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip'
            }
        }

        stage('Tests: JUnit') {
            steps {
                sh 'cd key && ./gradlew --continue test' 
                junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
            }    
        }

        stage('Test: testProveRules') {
            steps {
                sh 'cd key && ./gradlew --continue testProveRules'
                junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
            }    
        }    

        stage('Test: testRunAllProofs') {
            steps {
                sh 'cd key && ./gradlew --continue testRunAllProofs' 
                junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
            }    
        }    

        stage('Docs') {
            steps{ sh 'key/scripts/jenkins/generateDoc.sh'}
        }
    }
}
