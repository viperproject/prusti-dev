pub async fn connect<D>(dst: D)
where
    D: std::convert::TryInto<u32>
{ //~ ERROR unsupported type
}

fn main(){}
