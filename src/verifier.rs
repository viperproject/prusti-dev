use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub fn new_silicon<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
    trace!("new_silicon");
    env.new_object("viper/silicon/Silicon", "()V", &[])
}

pub fn new_carbon<'a>(env: &JNIEnv<'a>) -> Result<JObject<'a>, Error> {
    trace!("new_carbon");
    env.new_object("viper/carbon/CarbonVerifier", "()V", &[])
}

pub fn parse_command_line<'a>(
    env: &'a JNIEnv,
    verifier: JObject,
    command_line_args: JObject,
) -> Result<JValue<'a>, Error> {
    trace!("parse_command_line");
    env.call_method(
        verifier,
        "parseCommandLine",
        "(Lscala/collection/Seq;)V",
        &[JValue::Object(command_line_args)],
    )
}

pub fn start<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    trace!("start");
    env.call_method(verifier, "start", "()V", &[]).map(|_| ())
}

pub fn reset<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    trace!("reset");
    env.call_method(verifier, "reset", "()V", &[]).map(|_| ())
}

pub fn stop<'a>(env: &'a JNIEnv, verifier: JObject) -> Result<(), Error> {
    trace!("stop");
    env.call_method(verifier, "stop", "()V", &[]).map(|_| ())
}

pub fn verify<'a>(env: &'a JNIEnv, verifier: JObject, prog: JValue) -> Result<JObject<'a>, Error> {
    trace!("verify");
    env.call_method(
        verifier,
        "verify",
        "(Lviper/silver/ast/Program;)Lviper/silver/verifier/VerificationResult;",
        &[prog],
    ).and_then(|x| x.l())
}
