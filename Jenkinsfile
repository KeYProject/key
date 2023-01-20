pipeline {
    agent {
        docker {
            label "bwcloud"
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
                sh 'scripts/jenkins/startupClean.sh'
            }
        }

        stage('Compile') {
            steps { 
                sh './gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip'
            }
        }

        stage('Test: JUnit') {
            steps {
                sh './gradlew --continue test -x key.core.symbolic_execution:test -x key.core.proof_references:test'
            }
        }

        stage('Test: testProveRules') {
            steps {
                sh './gradlew --continue testProveRules'
            }
        }

        stage('Test: testRunAllFunProofs') {
            steps {
                sh './gradlew --continue testRunAllFunProofs'
            }
        }

        stage('Test: testRunAllInfProofs') {
            steps {
                sh './gradlew --continue testRunAllInfProofs'
            }
        }

        stage('Test: Optional Features') {
            steps {
                catchError(buildResult: 'SUCCESS', stageResult: 'FAILURE') {
                    sh './gradlew --continue key.core.symbolic_execution:test key.core.proof_references:test'
                }
            }
        }

        stage('Check Formatting') {
            steps {
                catchError(buildResult: 'SUCCESS', stageResult: 'FAILURE') {
                    sh './gradlew --continue spotlessCheck'
                }
            }
        }

        stage('Docs') {
            steps{ sh 'scripts/jenkins/generateDoc.sh'}
        }
    }

    post {
        always {
            junit(testResults: '*/build/test-results/*/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
        }
    }
}
