use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

fn new_silicon<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
    env.new_object("viper/silicon/Silicon", "()V", &[])
}

fn new_carbon<'a>(env: &JNIEnv<'a>) -> Result<JObject<'a>, Error> {
    env.new_object("viper/carbon/CarbonVerifier", "()V", &[])
}

fn parse_command_line<'a>(
    env: &'a JNIEnv,
    verifier: JObject,
    args: JValue,
) -> Result<JValue<'a>, Error> {
    env.call_method(
        verifier,
        "parseCommandLine",
        "(Lscala/collection/Seq;)V",
        &[args],
    )
}

fn start<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "start", "()V", &[])
}

fn restart<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "restart", "()V", &[])
}

fn stop<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "stop", "()V", &[])
}

fn verify<'a>(env: &'a JNIEnv, verifier: JObject, prog: JValue) -> Result<JValue<'a>, Error> {
    env.call_method(
        verifier,
        "verify",
        "(Lviper/silver/ast/Program;)Lviper/silver/verifier/VerificationResult",
        &[prog],
    )
}
