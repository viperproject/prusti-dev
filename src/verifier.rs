use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub fn new_silicon<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
    env.new_object("viper/silicon/Silicon", "()V", &[])
}

pub fn new_carbon<'a>(env: &JNIEnv<'a>) -> Result<JObject<'a>, Error> {
    env.new_object("viper/carbon/CarbonVerifier", "()V", &[])
}

pub fn parse_command_line<'a>(
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

pub fn start<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "start", "()V", &[])
}

pub fn restart<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "restart", "()V", &[])
}

pub fn stop<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<JValue<'a>, Error> {
    env.call_method(verifier, "stop", "()V", &[])
}

pub fn verify<'a>(env: &'a JNIEnv, verifier: JObject, prog: JValue) -> Result<JValue<'a>, Error> {
    env.call_method(
        verifier,
        "verify",
        "(Lviper/silver/ast/Program;)Lviper/silver/verifier/VerificationResult",
        &[prog],
    )
}
