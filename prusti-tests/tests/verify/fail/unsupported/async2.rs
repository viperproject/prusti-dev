pub struct QueryClient {
}
impl QueryClient
{
    pub async fn accounts(
        &mut self,
        _request: u32
    ) -> Result<u32, u32> { //~ ERROR unsupported type
        unimplemented!()
    }
}

fn main() {}
