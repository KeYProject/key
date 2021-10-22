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
          dir 'key'
          sh './gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip'
          }
    }

    stage('Tests: JUnit') {
      steps {
        dir 'key'
        sh './gradlew --continue test testProveRules testRunAllProofs' 
        junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
      }    
    }

    stage('Test: testProveRules') {
      steps {
        dir 'key'
        sh './gradlew --continue testProveRules' 
      }    
    }    

    stage('Test: testRunAllProofs') {
      steps {
        dir 'key'
        sh './gradlew --continue testRunAllProofs' 
      }    
    }    

    stage('Docs') {
        steps{sh 'key/scripts/jenkins/generateDoc.sh'}
    }
  }
}
