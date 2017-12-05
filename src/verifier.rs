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
    command_line_args: JObject,
) -> Result<JValue<'a>, Error> {
    env.call_method(
        verifier,
        "parseCommandLine",
        "(Lscala/collection/Seq;)V",
        &[JValue::Object(command_line_args)],
    )
}

pub fn start<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    env.call_method(verifier, "start", "()V", &[]).map(|_| ())
}

pub fn restart<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    env.call_method(verifier, "restart", "()V", &[]).map(|_| ())
}

pub fn stop<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    env.call_method(verifier, "stop", "()V", &[]).map(|_| ())
}

pub fn verify<'a>(env: &'a JNIEnv, verifier: JObject, prog: JValue) -> Result<JObject<'a>, Error> {
    env.call_method(
        verifier,
        "verify",
        "(Lviper/silver/ast/Program;)Lviper/silver/verifier/VerificationResult;",
        &[prog],
    ).and_then(|x| x.l())
}
