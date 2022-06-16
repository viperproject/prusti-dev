pub struct QueryClient {
}
impl QueryClient
{
    pub async fn accounts( //~ ERROR unsupported type
        &mut self,
        _request: u32
    ) -> Result<u32, u32> { //~ ERROR generator fields are not currently supported
        unimplemented!()
    }
}

fn main() {}
